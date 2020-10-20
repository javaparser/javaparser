package com.github.javaparser.symbolsolver.resolution.promotion;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.typeinference.TypeHelper;

/*
 * Numeric conditional expressions are standalone expressions (§15.2).
 * The type of a numeric conditional expression is determined as follows:
 * If the second and third operands have the same type, then that is the type of the conditional expression.
 * If one of the second and third operands is of primitive type T, and the type of the other is the result of applying boxing conversion (§5.1.7) to T, then the type of the conditional expression is T.
 * If one of the operands is of type byte or Byte and the other is of type short or Short, then the type of the conditional expression is short.
 * If one of the operands is of type T where T is byte, short, or char, and the other operand is a constant expression (§15.28) of type int whose value is representable in type T, then the type of the conditional expression is T.
 * If one of the operands is of type T, where T is Byte, Short, or Character, and the other operand is a constant expression of type int whose value is representable in the type U which is the result of applying unboxing conversion to T, then the type of the conditional expression is U.
 * Otherwise, binary numeric promotion (§5.6.2) is applied to the operand types, and the type of the conditional expression is the promoted type of the second and third operands.
 */
public class NumericConditionalExprHandler implements ConditionalExprHandler {

    private static Map<ResolvedType, List<ResolvedType>> NumericConverter = new HashMap();
    static {
        // first type is the type of the resolution
        // the list indicates the types that can be resolved in the type specified as
        // key
        NumericConverter.put(ResolvedPrimitiveType.SHORT,
                Arrays.asList(ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.BYTE));
    }

    ResolvedType thenExpr;
    ResolvedType elseExpr;

    public NumericConditionalExprHandler(ResolvedType thenExpr, ResolvedType elseExpr) {
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }

    @Override
    public ResolvedType resolveType() {
        String qnameTypeThenExpr = thenExpr.isPrimitive() ? thenExpr.asPrimitive().describe()
                : thenExpr.asReferenceType().describe();
        String qnameTypeElseExpr = elseExpr.isPrimitive() ? elseExpr.asPrimitive().describe()
                : elseExpr.asReferenceType().describe();
        if (qnameTypeThenExpr.equals(qnameTypeElseExpr)) {
            return thenExpr;
        } else if ((thenExpr.isPrimitive() && elseExpr.isReferenceType()
                && TypeHelper.isUnboxableTo(((ResolvedPrimitiveType) ResolvedPrimitiveType.byName(qnameTypeThenExpr)),
                        elseExpr.asReferenceType()))) {
            return thenExpr;
        } else if ((elseExpr.isPrimitive() && thenExpr.isReferenceType()
                && TypeHelper.isUnboxableTo(((ResolvedPrimitiveType) ResolvedPrimitiveType.byName(qnameTypeElseExpr)),
                        thenExpr.asReferenceType()))) {
            return elseExpr;
        } else if (isResolvableTo(ResolvedPrimitiveType.SHORT, thenExpr)
                || isResolvableTo(ResolvedPrimitiveType.SHORT, elseExpr)) {
            return ResolvedPrimitiveType.SHORT;
        }
        // If one of the operands is of type T where T is byte, short, or char, and the
        // other operand is a constant expression (§15.28) of type int whose value is
        // representable in type T, then the type of the conditional expression is T
        // How can we know if the constant expression of type int is representable in
        // type T ?

        // If one of the operands is of type T, where T is Byte, Short, or Character,
        // and the other operand is a constant expression of type int whose value is
        // representable in the type U which is the result of applying unboxing
        // conversion to T, then the type of the conditional expression is U.
        // How can we know it?

        // Otherwise, binary numeric promotion (§5.6.2) is applied to the operand types,
        // and the type of the conditional expression is the promoted type of the second
        // and third operands.
        ResolvedPrimitiveType PrimitiveThenExpr = thenExpr.isPrimitive() ? thenExpr.asPrimitive()
                : TypeHelper.toUnboxedType(thenExpr.asReferenceType());
        ResolvedPrimitiveType PrimitiveElseExpr = elseExpr.isPrimitive() ? elseExpr.asPrimitive()
                : TypeHelper.toUnboxedType(elseExpr.asReferenceType());
        return PrimitiveThenExpr.bnp(PrimitiveElseExpr);
    }

    protected boolean in(ResolvedType type, ResolvedPrimitiveType[] types) {
        return type.isPrimitive() && type.asPrimitive().in(types);
    }

    protected boolean isResolvableTo(ResolvedPrimitiveType toType, ResolvedType resolvedType) {
        // force to verify boxed type
        return isResolvableTo(toType, resolvedType, true);
    }

    protected boolean isResolvableTo(ResolvedPrimitiveType toType, ResolvedType resolvedType, boolean verifyBoxedType) {
        return NumericConverter.entrySet().stream().filter(e -> e.getKey() == toType)
                .flatMap(entry -> entry.getValue().stream())
                .anyMatch(rt -> rt == resolvedType || (verifyBoxedType && resolvedType.isReferenceType()
                        && TypeHelper.toUnboxedType(resolvedType.asReferenceType()) == toType));
    }
}
