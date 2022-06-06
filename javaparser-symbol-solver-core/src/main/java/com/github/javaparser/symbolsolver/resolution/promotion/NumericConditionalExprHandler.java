package com.github.javaparser.symbolsolver.resolution.promotion;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;

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
    
    private static ResolvedPrimitiveType[] resolvedPrimitiveTypeSubList = new ResolvedPrimitiveType[] {ResolvedPrimitiveType.BYTE, ResolvedPrimitiveType.SHORT, ResolvedPrimitiveType.CHAR};

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
        }
        /*
         * If one of the second and third operands is of primitive type T, and the type of the other is the result of
         * applying boxing conversion (§5.1.7) to T, then the type of the conditional expression is T.
         */
        if (thenExpr.isPrimitive() && elseExpr.isReferenceType()
                && elseExpr.asReferenceType()
                        .isUnboxableTo((ResolvedPrimitiveType) ResolvedPrimitiveType.byName(qnameTypeThenExpr))) {
            return thenExpr;
        }
        if (elseExpr.isPrimitive() && thenExpr.isReferenceType()
                && thenExpr.asReferenceType()
                        .isUnboxableTo((ResolvedPrimitiveType) ResolvedPrimitiveType.byName(qnameTypeElseExpr))) {
            return elseExpr;
        }
        /*
         * If one of the operands is of type byte or Byte and the other is of type short or Short, then the type of the
         * conditional expression is short.
         */
        
        if ((isResolvableTo(ResolvedPrimitiveType.SHORT, thenExpr) && relaxMatch(elseExpr, ResolvedPrimitiveType.BYTE))
                || (isResolvableTo(ResolvedPrimitiveType.SHORT, elseExpr) && relaxMatch(thenExpr, ResolvedPrimitiveType.BYTE))) {
            return ResolvedPrimitiveType.SHORT;
        }
        
//        if ((in(thenExpr, ResolvedPrimitiveType.SHORT) && in(elseExpr, ResolvedPrimitiveType.BYTE))
//                || (in(elseExpr, ResolvedPrimitiveType.SHORT) && in(thenExpr, ResolvedPrimitiveType.BYTE))) {
//            return ResolvedPrimitiveType.SHORT;
//        }
        
        // If one of the operands is of type T where T is byte, short, or char, and the
        // other operand is a constant expression (§15.28) of type int whose value is
        // representable in type T, then the type of the conditional expression is T
        // How can we know if the constant expression of type int is representable in
        // type T ?
        
        if (thenExpr.isPrimitive() && elseExpr.isPrimitive()) {
            if (((ResolvedPrimitiveType)thenExpr).in(resolvedPrimitiveTypeSubList)
                && ((ResolvedPrimitiveType)elseExpr).equals(ResolvedPrimitiveType.INT)) {
                return thenExpr;
            } else if (((ResolvedPrimitiveType)elseExpr).in(resolvedPrimitiveTypeSubList)
                && ((ResolvedPrimitiveType)thenExpr).equals(ResolvedPrimitiveType.INT)) {
                return elseExpr;
            }
        }

        // If one of the operands is of type T, where T is Byte, Short, or Character,
        // and the other operand is a constant expression of type int whose value is
        // representable in the type U which is the result of applying unboxing
        // conversion to T, then the type of the conditional expression is U.
        // How can we know it?
        
        if (thenExpr.isReference() && elseExpr.isPrimitive()
                && thenExpr.asReferenceType().isUnboxable()
                && thenExpr.asReferenceType().toUnboxedType().get().in(resolvedPrimitiveTypeSubList)
                && ((ResolvedPrimitiveType)elseExpr).equals(ResolvedPrimitiveType.INT)) {
            return thenExpr.asReferenceType().toUnboxedType().get();
        } else if (elseExpr.isReference() && thenExpr.isPrimitive()
                && elseExpr.asReferenceType().isUnboxable()
                && elseExpr.asReferenceType().toUnboxedType().get().in(resolvedPrimitiveTypeSubList)
                && ((ResolvedPrimitiveType)thenExpr).equals(ResolvedPrimitiveType.INT)) {
            return elseExpr.asReferenceType().toUnboxedType().get();
        }

        // Otherwise, binary numeric promotion (§5.6.2) is applied to the operand types,
        // and the type of the conditional expression is the promoted type of the second
        // and third operands.
        ResolvedPrimitiveType PrimitiveThenExpr = thenExpr.isPrimitive() ? thenExpr.asPrimitive()
                : thenExpr.asReferenceType().toUnboxedType().get();
        ResolvedPrimitiveType PrimitiveElseExpr = elseExpr.isPrimitive() ? elseExpr.asPrimitive()
                : elseExpr.asReferenceType().toUnboxedType().get();
        return PrimitiveThenExpr.bnp(PrimitiveElseExpr);
    }

    /*
     * Verify if the {code ResolvedType} is equals to one of the specified primitive types
     */
    protected boolean exactMatch(ResolvedType type, ResolvedPrimitiveType... types) {
        return type.isPrimitive() && type.asPrimitive().in(types);
    }
    
    protected boolean relaxMatch(ResolvedType type, ResolvedPrimitiveType... types) {
        return exactMatch(type, types) || (type.isReferenceType() && Arrays.stream(types).anyMatch(t -> type.asReferenceType().getQualifiedName().equals(t.getBoxTypeQName())));
    }
    
    /*
     * Verify if the {code ResolvedType} can be resolve to the specified primitive type
     */
    protected boolean isResolvableTo(ResolvedPrimitiveType toType, ResolvedType resolvedType) {
        // force to verify boxed type
        return isResolvableTo(toType, resolvedType, true);
    }

    protected boolean isResolvableTo(ResolvedPrimitiveType toType, ResolvedType resolvedType, boolean verifyBoxedType) {
        return NumericConverter.entrySet().stream().filter(e -> e.getKey() == toType)
                .flatMap(entry -> entry.getValue().stream())
                .anyMatch(rt -> rt == resolvedType || (verifyBoxedType && resolvedType.isReferenceType()
                        && resolvedType.asReferenceType().toUnboxedType().get() == toType));
    }
}
