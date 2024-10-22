import { verify } from "crypto";
import type {
  DeclFun,
  Expr,
  Program,
  Type,
  TypeBool,
  TypeFun,
  TypeNat,
  PatternVar,
  PatternVariant,
  Pattern,
  TypeRecord,
  TypeTuple,
  TypeRef,
  TypeBottom,
  TypeList,
  TypeSum,
  TypeCast,
  TypeVariant,
  TypeAuto,
} from "./ast";

interface Context {
  symbolTable: Map<string, Type>;
  hasMain: boolean;
  exceptionType: Type | null;
}

export class TypeChecker {
  public generateEmptyContext(): Context {
    return {
      symbolTable: new Map(),
      hasMain: false,
      exceptionType: null,
    };
  }
  constructor() {}

  private static TYPE_NAT: TypeNat = {type: "TypeNat"};
  private static TYPE_BOOL: TypeBool = {type: "TypeBool"};
  private static TYPE_BOT: TypeBottom = {type: 'TypeBottom'};
  private static TYPE_LIST = (t: Type): TypeList => ({type: 'TypeList', elementType: t});
  private static TYPE_SUM = (left: Type, right: Type): TypeSum => ({
    type: 'TypeSum',
    left,
    right,
  });

  private static TYPE_REF = (type: Type): TypeRef => ({
    type: 'TypeRef',
    referredType: type,
  });

  public typecheckProgram(ast: Program): void {
    const ctx = this.generateEmptyContext();
    for (const decl of ast.declarations) {
      switch (decl.type) {
        case "DeclFun": {
          ctx.symbolTable.set(decl.name, {
            type: "TypeFun",
            parametersTypes: decl.parameters.map((param) => param.paramType),
            returnType: decl.returnType!,
          });
          this.typecheckFunctionDecl(decl, ctx);
          break;
        }
        case "DeclExceptionType": {
          ctx.exceptionType = decl.exceptionType;
          break;
        }
        case "DeclExceptionVariant": {
          ctx.exceptionType = {
            type: "TypeVariant",
            fieldTypes: [
              {
                type: "VariantFieldType",
                label: decl.name,
                fieldType: decl.variantType,
              },
            ],
          };
          break;
        }
      }
    }

    if (!ctx.hasMain) {
      throw new Error(TypeChecker.Errors.MISSING_MAIN);
    }
    console.log("Everything typechecks!");
  }

  private typecheckFunctionDecl(decl: DeclFun, ctx: Context): void {
    const {name, parameters, returnValue, returnType} = decl;
    if (name === "main") {
      ctx.hasMain = true;
    }
    const param = parameters[0];
    const newSymbols = new Map(ctx.symbolTable);
    newSymbols.set(param.name, param.paramType);
    const newContext = {...ctx, symbolTable: newSymbols};
    const bodyType = this.typecheckExpr(returnValue, newContext, returnType!);
    this.verifyTypesMatch(bodyType, returnType!);
  }

  public typecheckExpr(
    expr: Expr,
    ctx: Context,
    expectedType: Type | null = null
  ): Type {
    switch (expr.type) {
      case "Var": {
        if (!ctx.symbolTable.has(expr.name)) {
          throw new Error(TypeChecker.Errors.UNDEFINED_VARIABLE);
        }

        return ctx.symbolTable.get(expr.name)!;
      }
      case "Succ": {
        const exprType = this.typecheckExpr(expr.expr, ctx, {type: "TypeNat"});
        this.verifyTypesMatch(TypeChecker.TYPE_NAT, exprType);
        return TypeChecker.TYPE_NAT;
      }
      case "ConstBool": {
        return TypeChecker.TYPE_BOOL;
      }
      case "ConstInt": {
        return TypeChecker.TYPE_NAT;
      }
      case "If": {
        const condType = this.typecheckExpr(expr.condition, ctx, TypeChecker.TYPE_BOOL);
        this.verifyTypesMatch(condType, TypeChecker.TYPE_BOOL);
        const thenType = this.typecheckExpr(expr.thenExpr, ctx, expectedType);
        const elseType = this.typecheckExpr(expr.elseExpr, ctx, expectedType);
        this.verifyTypesMatch(thenType, elseType);
        return thenType;
      }
      case "NatIsZero": {
        const exprType = this.typecheckExpr(expr.expr, ctx);
        this.verifyTypesMatch(TypeChecker.TYPE_NAT, exprType);
        return TypeChecker.TYPE_BOOL;
      }
      case "NatRec": {
        const {n, initial, step} = expr;
        const nType = this.typecheckExpr(n, ctx);
        this.verifyTypesMatch(TypeChecker.TYPE_NAT, nType);
        const initialType = this.typecheckExpr(initial, ctx);
        const stepExpectedType: TypeFun = {
          type: "TypeFun",
          parametersTypes: [TypeChecker.TYPE_NAT],
          returnType: {
            type: "TypeFun",
            parametersTypes: [initialType],
            returnType: initialType,
          },
        };
        const stepActualType = this.typecheckExpr(step, ctx);
        this.verifyTypesMatch(stepExpectedType, stepActualType);
        return initialType;
      }
      case "Abstraction": {
        if (expectedType && expectedType.type !== "TypeFun") {
          if (expectedType.type !== "TypeAuto") {
            throw new Error(TypeChecker.Errors.UNEXPECTED_LAMBDA);
          } else {
            expectedType = null;
          }
        }
        const {parameters, returnValue} = expr;
        const param = parameters[0];
        const newSymbols = new Map(ctx.symbolTable);
        newSymbols.set(param.name, param.paramType);

        const newContext = {...ctx, symbolTable: newSymbols};
        const bodyType = this.typecheckExpr(
          returnValue,
          newContext,
          expectedType?.returnType ?? null
        );
        return {
          type: "TypeFun",
          parametersTypes: [param.paramType],
          returnType: bodyType,
        };
      }
      case "Application": {
        const {function: func, arguments: args} = expr;
        const funcType = this.typecheckExpr(func, ctx, null);
        if (funcType.type !== "TypeFun") {
          throw new Error(TypeChecker.Errors.NOT_A_FUNCTION);
        }
        const argType = this.typecheckExpr(args[0], ctx, funcType.parametersTypes[0]);
        this.verifyTypesMatch(funcType.parametersTypes[0], argType);
        if (expectedType) {
          this.verifyTypesMatch(funcType.returnType, expectedType);
        }
        return (funcType as TypeFun).returnType;
      }
      case "Unit": {
        return {type: "TypeUnit"};
      }
      case "Tuple": {
        if (expectedType && expectedType.type !== 'TypeTuple') {
          throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_TUPLE);
        }
        // only pairs
        const [expr1, expr2] = expr.exprs;
        const type1 = this.typecheckExpr(expr1, ctx, expectedType?.types[0] ?? null);
        const type2 = this.typecheckExpr(expr2, ctx, expectedType?.types[1] ?? null);
        return {
          type: 'TypeTuple',
          types: [type1, type2],
        };
      }
      case "Record": {
        const fields = new Map<string, Type>();
        expr.bindings.forEach((binding) => {
          fields.set(binding.name, this.typecheckExpr(binding.expr, ctx));
        });
        return {
          type: "TypeRecord",
          fieldTypes: Array.from(fields.entries()).map(
            ([label, fieldType]) => ({
              type: "RecordFieldType",
              label,
              fieldType,
            })
          ),
        };
      }
      case "Let": {
        const {body, patternBindings} = expr;
        for (const binding of patternBindings) {
          if (binding.pattern.type !== "PatternVar")
            throw new Error(TypeChecker.Errors.UNEXPECTED_TYPE_FOR_EXPRESSION);
          const rhsType = this.typecheckExpr(binding.rhs, ctx, null);
          ctx.symbolTable.set(binding.pattern.name, rhsType);
        }
        const bodyType = this.typecheckExpr(body, ctx, expectedType);
        return bodyType;
      }
      case 'DotRecord': {
        const {expr: record, label} = expr;
        const recordType = this.typecheckExpr(record, ctx, null);
        if (recordType.type !== 'TypeRecord') {
          throw new Error(TypeChecker.Errors.ERROR_NOT_A_RECORD);
        }
        const fieldType = recordType.fieldTypes.find(
          (field) => field.label === label
        );
        if (fieldType == null) {
          throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_FIELD_ACCESS);
        }
        return fieldType.fieldType;
      }
      case "DotTuple": {
        const tupleType = this.typecheckExpr(expr.expr, ctx);
        if (tupleType.type !== "TypeTuple" || tupleType.types.length !== 2) {
          throw new Error(TypeChecker.Errors.ERROR_NOT_A_TUPLE);
        }
        if (expr.index < 1 || expr.index > tupleType.types.length) {
          throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_TUPLE);
        }
        return tupleType.types[expr.index - 1];
      }

      case 'Inl': {
        if (expectedType && expectedType.type !== 'TypeSum') {
          throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_INJECTION);
        }
        const {expr: expression} = expr;
        const actualType = this.typecheckExpr(
          expression,
          ctx,
          expectedType?.left ?? null
        );
        if (expectedType) {
          this.verifyTypesMatch(expectedType.left, actualType);
          return expectedType;
        } else {
          return TypeChecker.TYPE_SUM(actualType, TypeChecker.TYPE_BOT);
        }
      }
      case 'Inr': {
        if (expectedType && expectedType.type !== 'TypeSum') {
          throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_INJECTION);
        }
        const {expr: expression} = expr;
        const actualType = this.typecheckExpr(
          expression,
          ctx,
          expectedType?.right ?? null
        );
        if (expectedType) {
          this.verifyTypesMatch(expectedType.right, actualType);
          return expectedType;
        } else {
          return TypeChecker.TYPE_SUM(TypeChecker.TYPE_BOT, actualType);
        }
      }
      case 'Match': {
        const {cases, expr: expression} = expr;
        const exprType = this.typecheckExpr(expression, ctx, null);
        if (cases.length === 0) {
          throw new Error(TypeChecker.Errors.ERROR_ILLEGAL_EMPTY_MATCHING);
        }
        let caseBodyExpectedType: Type | null = expectedType;
        for (const matchCase of cases) {
          const extendedCtx = this.typecheckPattern(matchCase.pattern, exprType, ctx);
          const inferredType = this.typecheckExpr(
            matchCase.expr,
            extendedCtx,
            expectedType
          );
          if (caseBodyExpectedType != null) {
            this.verifyTypesMatch(caseBodyExpectedType, inferredType);
          } else {
            caseBodyExpectedType = inferredType;
          }
        }
        if (
          !this.isExhaustive(
            exprType,
            cases.map((case_) => case_.pattern)
          )
        ) {
          throw new Error(TypeChecker.Errors.ERROR_NONEXHAUSTIVE_MATCH_PATTERNS);
        }
        return caseBodyExpectedType!;
      }
      case "TypeAscription": {
        const exprType = this.typecheckExpr(expr.expr, ctx, expr.ascribedType);
        this.verifyTypesMatch(expr.ascribedType, exprType);
        if (expr.ascribedType.type === "TypeSum") {
          if (!expr.ascribedType.left || !expr.ascribedType.right) {
            throw new Error(TypeChecker.Errors.ERROR_AMBIGUOUS_SUM_TYPE);
          }
          if (expr.expr.type === "Inl") {
            this.verifyTypesMatch(expr.ascribedType.left, exprType);
          } else {
            this.verifyTypesMatch(expr.ascribedType.right, exprType);
          }
        }
        return expr.ascribedType;
      }

      case 'List': {
        if (expectedType && expectedType.type !== 'TypeList') {
          throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_LIST);
        }
        const {exprs} = expr;
        let elementExpectedType: Type | null = expectedType;
        for (const element of exprs) {
          const inferredType = this.typecheckExpr(
            element,
            ctx,
            expectedType?.elementType ?? null
          );
          if (elementExpectedType) {
            this.verifyTypesMatch(elementExpectedType, inferredType);
            if (
              elementExpectedType.type !== inferredType.type &&
              inferredType.type !== "TypeAuto"
            ) {
              throw new Error(TypeChecker.Errors.UNEXPECTED_TYPE_FOR_EXPRESSION);
            }
          } else {
            elementExpectedType = inferredType;
          }
        }
        return TypeChecker.TYPE_LIST(elementExpectedType ?? TypeChecker.TYPE_BOT);
      }

      case "Cons": {
        const headType = this.typecheckExpr(expr.head, ctx, null);
        const tailType = this.typecheckExpr(expr.tail, ctx, null);
        if (tailType.type !== "TypeList") {
          throw new Error(TypeChecker.Errors.ERROR_NOT_A_LIST);
        }
        if (tailType.elementType.type === "TypeBottom") {
          return {type: "TypeList", elementType: headType};
        }
        this.verifyTypesMatch(headType, tailType.elementType);
        return tailType;
      }

      case 'ListHead': {
        const {expr: expression} = expr;
        const exprType = this.typecheckExpr(
          expression,
          ctx,
          expectedType && TypeChecker.TYPE_LIST(expectedType)
        );
        if (exprType.type !== 'TypeList') {
          throw new Error(TypeChecker.Errors.ERROR_NOT_A_LIST);
        }
        return exprType.elementType;
      }
      case 'ListTail': {
        const {expr: expression} = expr;
        const exprType = this.typecheckExpr(
          expression,
          ctx,
          expectedType && TypeChecker.TYPE_LIST(expectedType)
        );
        if (exprType.type !== 'TypeList') {
          throw new Error(TypeChecker.Errors.ERROR_NOT_A_LIST);
        }
        return exprType;
      }
      case 'ListIsEmpty': {
        const {expr: expression} = expr;
        const exprType = this.typecheckExpr(
          expression,
          ctx,
          expectedType && TypeChecker.TYPE_LIST(expectedType)
        );
        if (exprType.type !== 'TypeList') {
          throw new Error(TypeChecker.Errors.ERROR_NOT_A_LIST);
        }
        return {type: "TypeBool"};
      }
      case 'Variant': {
        const {label, expr: value} = expr;
        let fieldExpectedType: Type | null = null;
        if (expectedType) {
          if (expectedType.type !== 'TypeVariant') {
            throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_VARIANT);
          }
          const field = expectedType.fieldTypes.find(
            (field) => field.label === label
          );
          if (field == undefined) {
            throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_VARIANT_LABEL);
          }
          fieldExpectedType = field.fieldType!;
        }
        const fieldType = this.typecheckExpr(value!, ctx, fieldExpectedType);
        if (fieldExpectedType) {
          this.verifyTypesMatch(fieldExpectedType, fieldType);
        }
        return (
          expectedType ?? {
            type: 'TypeVariant',
            fieldTypes: [{type: 'VariantFieldType', label, fieldType}],
          }
        );
      }
      case "Fix":
        const funcType = this.typecheckExpr(expr.expr, ctx, null);
        if (funcType.type !== "TypeFun") {
          throw new Error(TypeChecker.Errors.NOT_A_FUNCTION);
        }
        this.verifyTypesMatch(funcType.parametersTypes[0], funcType.returnType);
        return funcType.returnType;

      case "Sequence": {
        const {expr1, expr2} = expr;
        const Expr1Type = this.typecheckExpr(expr1, ctx, {type: "TypeUnit"});
        this.verifyTypesMatch({type: "TypeUnit"}, Expr1Type);
        const Expr2Type = this.typecheckExpr(expr2, ctx, expectedType);

        return Expr2Type;
      }
      case "Panic": {
        if (!expectedType) {
          return TypeChecker.TYPE_BOT;
        }
        return expectedType;
      }
      case "Assignment": {
        const { lhs, rhs } = expr;
        //here added
        let rhsType = this.typecheckExpr(rhs, ctx, null);
        let lhsType = this.typecheckExpr(lhs, ctx, {
          type: "TypeRef",
          referredType: rhsType,
        });
  
        if (lhsType.type !== "TypeRef") {
          //here added
          if (lhsType.type === "TypeAuto") {
            lhsType = {
              type: "TypeRef",
              referredType: rhsType,
            };
          } else {
            throw new Error(TypeChecker.Errors.ERROR_NOT_A_REFERENCE);
          }
        }
        this.verifyTypesMatch(lhsType.referredType, rhsType);
  
        return { type: "TypeUnit" };
      }
      case 'Reference': {
        const {expr: initialValue} = expr;
        if (expectedType && expectedType.type === 'TypeRef') {
          expectedType = expectedType.referredType;
        }
        const exprType = this.typecheckExpr(initialValue, ctx, expectedType);
        return TypeChecker.TYPE_REF(exprType);
      }
      case 'Dereference': {
        let expectedTypeDeref: Type | null = null;
        if (expectedType) {
          expectedTypeDeref = {
            type: "TypeRef",
            referredType: expectedType,
          };
          let derefExp = this.typecheckExpr(expr.expr, ctx, expectedTypeDeref);

          if (derefExp.type !== "TypeRef") {
            if (derefExp.type !== "TypeAuto") {
              throw Error(TypeChecker.Errors.ERROR_NOT_A_REFERENCE);
            } else {
              derefExp = {
                type: "TypeRef",
                referredType: expectedTypeDeref?.referredType,
              };
            }
          }
          if (expectedType) {
            this.verifyTypesMatch(expectedTypeDeref!, derefExp);
          }
          return derefExp.referredType;
        } else {
          let derefExp = this.typecheckExpr(expr.expr, ctx, expectedTypeDeref);
          if (derefExp.type !== "TypeRef") {
            throw Error(TypeChecker.Errors.ERROR_NOT_A_REFERENCE);
          }
          this.verifyTypesMatch(expectedTypeDeref!, derefExp);
          return derefExp.referredType;
        }
      }
      case "ConstMemory": {
        if (expectedType && expectedType.type !== "TypeRef") {
          if (expectedType.type !== "TypeAuto") {
            throw Error(TypeChecker.Errors.ERROR_UNEXPECTED_MEMORY_ADDRESS);
          }
        }
        if (!expectedType) {
          throw Error(TypeChecker.Errors.ERROR_AMBIGUOUS_REFERENCE_TYPE);
        }
        return expectedType;
      }
      case "Throw": {
        if (ctx.exceptionType == null) {
          throw new Error(TypeChecker.Errors.ERROR_EXCEPTION_TYPE_NOT_DECLARED);
        }
        if (expectedType == null) {
          throw new Error(TypeChecker.Errors.ERROR_AMBIGUOUS_THROW_TYPE);
        }
        const {expr: throwExpr} = expr;
        const exprType = this.typecheckExpr(throwExpr, ctx, ctx.exceptionType);
        this.verifyTypesMatch(ctx.exceptionType, exprType);
        return expectedType;
      }
      case "TryWith": {
        const {tryExpr, fallbackExpr} = expr;
        const tryType = this.typecheckExpr(tryExpr, ctx, expectedType);
        const fallbackType = this.typecheckExpr(fallbackExpr, ctx, expectedType);
        this.verifyTypesMatch(tryType, fallbackType);
        return tryType;
      }
      case "TryCatch": {
        const {tryExpr, pattern, fallbackExpr} = expr;
        if (ctx.exceptionType == null) {
          throw new Error(TypeChecker.Errors.ERROR_EXCEPTION_TYPE_NOT_DECLARED);
        }
        this.typecheckPattern(pattern, ctx.exceptionType, ctx);
        const fallbackCtx = this.typecheckPattern(pattern, ctx.exceptionType, ctx);
        const tryType = this.typecheckExpr(tryExpr, ctx, expectedType);
        const fallbackType = this.typecheckExpr(
          fallbackExpr,
          fallbackCtx,
          expectedType
        );
        this.verifyTypesMatch(tryType, fallbackType);
        return tryType;
      }
      case 'TypeCast': {
        const {expr: expression, castType} = expr;
        const _ = this.typecheckExpr(expression, ctx, null);
        return castType;
      }
      default:
        throw new Error("Unknown sub type " + expr.type);
    }
  }

  private isPatternVar(pattern: Pattern): pattern is PatternVar {
    return pattern.type === "PatternVar";
  }

  private typecheckPattern(
    pattern: Pattern,
    expectedType: Type,
    ctx: Context
  ): Context {
    switch (pattern.type) {
      case "PatternVar": {
        const newSymbols = new Map(ctx.symbolTable);
        newSymbols.set(pattern.name, expectedType);
        return {
          ...ctx,
          symbolTable: newSymbols,
        };
      }
      case "PatternInl":
        if (expectedType.type !== "TypeSum") {
          throw new Error(TypeChecker.Errors.ERROR_ILLEGAL_EMPTY_MATCHING);
        }
        return this.typecheckPattern(pattern.pattern, expectedType.left, ctx);

      case "PatternInr":
        if (expectedType.type !== "TypeSum") {
          throw new Error(TypeChecker.Errors.ERROR_ILLEGAL_EMPTY_MATCHING);
        }
        return this.typecheckPattern(pattern.pattern, expectedType.right, ctx);
      case "PatternVariant":
        if (expectedType.type !== "TypeVariant") {
          throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_VARIANT);
        }
        const variantFieldType = expectedType.fieldTypes.find(
          (field) => field.label === pattern.label
        );
        if (!variantFieldType) {
          throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_VARIANT_LABEL);
        }
        return this.typecheckPattern(
          pattern.pattern!,
          variantFieldType.fieldType!,
          ctx
        );
      default:
        throw new Error("Unimplemented");
    }
  }

  private isExhaustive(type: Type, patterns: Pattern[]): boolean {
    const types = patterns.map((pattern) => pattern.type);
    if (types.some((type) => type === "PatternVar")) return true;
    switch (type.type) {
      case "TypeSum":
        return types.includes("PatternInl") && types.includes("PatternInr");

      case "TypeVariant": {
        const labelsUsed = (patterns as PatternVariant[]).map(
          (pattern) => pattern.label
        );
        const expectedLabels = type.fieldTypes.map((field) => field.label);
        return expectedLabels.every(labelsUsed.includes);
      } default:
        return false;
    }
  }

  private verifyTypesMatch(expected: Type | null, actual: Type) {
    if (expected == null) return;

    if (expected.type === 'TypeTop') {
      return true;
    }
    if (actual.type === 'TypeBottom') {
      return true;
    }

    if (expected.type !== actual.type) {
      if (expected.type === "TypeAuto" || actual.type === "TypeAuto") {
        return;
      }
      if (expected.type === "TypeBottom" || actual.type === "TypeTop") {
        throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_SUBTYPE);
      }

      if (expected.type !== "TypeTuple" && actual.type === "TypeTuple") {
        throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_TUPLE);
      }

      if (expected.type === "TypeTuple" && actual.type !== "TypeTuple") {
        throw new Error(TypeChecker.Errors.ERROR_NOT_A_TUPLE);
      }
      if (expected.type !== "TypeRecord" && actual.type === "TypeRecord") {
        throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_RECORD);
      }

      if (expected.type === "TypeRecord" && actual.type !== "TypeRecord") {
        throw new Error(TypeChecker.Errors.ERROR_NOT_A_RECORD);
      }
      if (expected.type !== "TypeFun" && actual.type === "TypeFun") {
        throw new Error(TypeChecker.Errors.UNEXPECTED_LAMBDA);
      }

      if (expected.type !== "TypeList" && actual.type === "TypeList") {
        throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_LIST);
      }
    } else if (expected.type === actual.type) {
      // Some types still require additional checks for complex internal structure
      switch (expected.type) {
        case "TypeFun": {
          try {
            this.verifyTypesMatch(
              expected.parametersTypes[0],
              (actual as TypeFun).parametersTypes[0]
            );
          } catch {
            throw new Error(TypeChecker.Errors.UNEXPECTED_TYPE_FOR_PARAMETER);
          }
          this.verifyTypesMatch(expected.returnType, (actual as TypeFun).returnType);
          return true;
        }
        case 'TypeTuple': {
          // pairs, so guaranteed to be the same length
          const [expected1, expected2] = expected.types;
          const [actual1, actual2] = (actual as TypeTuple).types;
          this.verifyTypesMatch(expected1, actual1);
          this.verifyTypesMatch(expected2, actual2);
          return true;
        }
        case 'TypeRecord': {
          const actualFields = (actual as TypeRecord).fieldTypes;
          for (const {label, fieldType} of expected.fieldTypes) {
            const actualField = actualFields.find((f) => f.label === label);
            if (actualField == null) {
              // Expected a field but did not find it
              throw new Error(TypeChecker.Errors.ERROR_MISSING_RECORD_FIELDS);
            }
            this.verifyTypesMatch(fieldType, actualField.fieldType);
          }

          if (
            expected.fieldTypes.length !==
            (actual as TypeRecord).fieldTypes.length
          ) {
            if (
              expected.fieldTypes.length >
              (actual as TypeRecord).fieldTypes.length
            ) {
              throw new Error(TypeChecker.Errors.ERROR_MISSING_RECORD_FIELDS);
            } else {
              return true;
            }
          }

          return true;
        }
        case 'TypeList': {
          this.verifyTypesMatch(
            expected.elementType,
            (actual as TypeList).elementType
          );
          return true;
        }
        case 'TypeVariant': {
          // Less fields are ok, more are not
          for (const {label, fieldType} of (actual as TypeVariant).fieldTypes) {
            const variant = expected.fieldTypes.find(
              (fieldType) => fieldType.label === label
            );
            if (!variant) {
              throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_VARIANT_LABEL);
            }
            const actualVariant = (actual as TypeVariant).fieldTypes.find(
              (fieldType) => fieldType.label === label
            );
            this.verifyTypesMatch(variant.fieldType!, actualVariant?.fieldType!);
          }
          return true;
        }
        case 'TypeRef': {
          this.verifyTypesMatch(
            expected.referredType,
            (actual as TypeRef).referredType
          );
          this.verifyTypesMatch(
            (actual as TypeRef).referredType,
            expected.referredType
          );
          return true;
        }
        case 'TypeSum': {
          this.verifyTypesMatch(expected.left, (actual as TypeSum).left);
          this.verifyTypesMatch(expected.right, (actual as TypeSum).right);
        }
        default:
          return true;
      }
    }
    throw new Error(TypeChecker.Errors.ERROR_UNEXPECTED_SUBTYPE);
  }

  private static Errors = {
    UNEXPECTED_TYPE_FOR_PARAMETER: "ERROR_UNEXPECTED_TYPE_FOR_PARAMETER",
    UNEXPECTED_TYPE_FOR_EXPRESSION: "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
    UNEXPECTED_LAMBDA: "ERROR_UNEXPECTED_LAMBDA",
    NOT_A_FUNCTION: "ERROR_NOT_A_FUNCTION",
    UNDEFINED_VARIABLE: "ERROR_UNDEFINED_VARIABLE",
    MISSING_MAIN: "ERROR_MISSING_MAIN",
    ERROR_MISSING_RECORD_FIELDS: "ERROR_MISSING_RECORD_FIELDS",
    ERROR_UNEXPECTED_RECORD_FIELDS: "ERROR_UNEXPECTED_RECORD_FIELDS",
    ERROR_UNEXPECTED_RECORD: "ERROR_UNEXPECTED_RECORD",
    ERROR_NOT_A_RECORD: "ERROR_NOT_A_RECORD",
    ERROR_UNEXPECTED_FIELD_ACCESS: "ERROR_UNEXPECTED_FIELD_ACCESS",
    ERROR_UNEXPECTED_TUPLE: "ERROR_UNEXPECTED_TUPLE",
    ERROR_NOT_A_TUPLE: "ERROR_NOT_A_TUPLE",
    ERROR_AMBIGUOUS_SUM_TYPE: "ERROR_AMBIGUOUS_SUM_TYPE",
    ERROR_AMBIGUOUS_LIST_TYPE: "ERROR_AMBIGUOUS_LIST_TYPE",
    ERROR_ILLEGAL_EMPTY_MATCHING: "ERROR_ILLEGAL_EMPTY_MATCHING",
    ERROR_NONEXHAUSTIVE_MATCH_PATTERNS: "ERROR_NONEXHAUSTIVE_MATCH_PATTERNS",
    ERROR_NOT_A_LIST: "ERROR_NOT_A_LIST",
    ERROR_UNEXPECTED_LIST: "ERROR_UNEXPECTED_LIST",
    ERROR_UNEXPECTED_INJECTION: "ERROR_UNEXPECTED_INJECTION",
    ERROR_UNEXPECTED_PATTERN_FOR: "ERROR_UNEXPECTED_PATTERN_FOR",
    ERROR_UNEXPECTED_VARIANT: "ERROR_UNEXPECTED_VARIANT",
    ERROR_UNEXPECTED_VARIANT_LABEL: "ERROR_UNEXPECTED_VARIANT_LABEL",
    ERROR_AMBIGUOUS_VARIANT_TYPE: "ERROR_AMBIGUOUS_VARIANT_TYPE",
    ERROR_EXCEPTION_TYPE_NOT_DECLARED: "ERROR_EXCEPTION_TYPE_NOT_DECLARED",
    ERROR_AMBIGUOUS_THROW_TYPE: "ERROR_AMBIGUOUS_THROW_TYPE",
    ERROR_AMBIGUOUS_REFERENCE_TYPE: "ERROR_AMBIGUOUS_REFERENCE_TYPE",
    ERROR_AMBIGUOUS_PANIC_TYPE: "ERROR_AMBIGUOUS_PANIC_TYPE",
    ERROR_NOT_A_REFERENCE: "ERROR_NOT_A_REFERENCE",
    ERROR_UNEXPECTED_MEMORY_ADDRESS: "ERROR_UNEXPECTED_MEMORY_ADDRESS",
    ERROR_UNEXPECTED_SUBTYPE: "ERROR_UNEXPECTED_SUBTYPE"
  };
}

export default TypeChecker;
