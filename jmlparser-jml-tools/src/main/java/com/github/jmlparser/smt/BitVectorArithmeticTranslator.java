package com.github.jmlparser.smt;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.jmlparser.smt.model.SExpr;
import com.github.jmlparser.smt.model.SmtType;

import java.math.BigInteger;

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
public class BitVectorArithmeticTranslator implements ArithmeticTranslator {
    int cnt = 0;
    private static final SmtTermFactory term = SmtTermFactory.INSTANCE;

    final SmtQuery smtLog;

    public BitVectorArithmeticTranslator(SmtQuery smtLog) {
        this.smtLog = smtLog;
    }

    @Override
    public SExpr binary(BinaryExpr.Operator operator, SExpr left, SExpr right) {
        switch (operator) {
            case IMPLICATION:
                return term.impl(left, right);
            case SUBTYPE:
                break;
            case RANGE:
                break;
            case SUB_LOCK:
                break;
            case SUB_LOCKE:
                break;
            case RIMPLICATION:
                return term.impl(right, left);
            case EQUIVALENCE:
                return term.equiv(left, right);
            case ANTIVALENCE:
                return term.not(term.equiv(left, right));
            case OR:
                return term.or(left, right);
            case AND:
                return term.and(left, right);
            case BINARY_OR:
                return term.bor(left, right);
            case BINARY_AND:
                return term.band(left, right);
            case XOR:
                return term.xor(left, right);
            case EQUALS:
                return term.equality(left, right);
            case NOT_EQUALS:
                return term.not(term.equality(left, right));
            case LESS:
                return term.lessThan(left, right);
            case GREATER:
                return term.greaterThan(left, right);
            case LESS_EQUALS:
                return term.lessOrEquals(left, right, true);
            case GREATER_EQUALS:
                return term.greaterOrEquals(left, right, true);
            case LEFT_SHIFT:
                return term.shiftLeft(left, right);
            case SIGNED_RIGHT_SHIFT:
                return term.shiftRight(left, right, true);
            case UNSIGNED_RIGHT_SHIFT:
                return term.shiftRight(left, right, true);
            case PLUS:
                return term.add(left, right);
            case MINUS:
                return term.subtract(left, right);
            case MULTIPLY:
                return term.multiply(left, right);
            case DIVIDE:
                return term.divide(left, right, true);
            case REMAINDER:
                return term.modulo(left, right, true);

        }
        return null;
    }

    @Override
    public SExpr makeChar(CharLiteralExpr n) {
        return term.makeBitvector(16, n.getValue().charAt(0));
    }

    @Override
    public SExpr unary(UnaryExpr.Operator operator, SExpr accept) {
        switch (operator) {
            case PLUS:
            case POSTFIX_INCREMENT:
            case POSTFIX_DECREMENT:
                return accept;
            case MINUS:
                return term.negate(accept);
            case PREFIX_INCREMENT:
                return term.add(accept, term.makeBitvector(32, 1));
            case PREFIX_DECREMENT:
                return term.subtract(accept, term.makeBitvector(32, 1));
            case LOGICAL_COMPLEMENT:
                return term.not(accept);
            case BITWISE_COMPLEMENT:
                return term.not(accept);
        }
        return accept;
    }

    @Override
    public SExpr makeLong(LongLiteralExpr n) {
        return term.makeBitvector(64, n.asLong());
    }

    @Override
    public SExpr makeInt(IntegerLiteralExpr n) {
        return term.makeBitvector(32, n.asInt());
    }

    @Override
    public SExpr makeInt(BigInteger i) {
        return term.makeBitvector(32, i);
    }

    @Override
    public SExpr makeIntVar() {
        String name = "__RAND_" + (++cnt);
        smtLog.declareConst(name, SmtType.BV32);
        return term.symbol(name);
    }

    @Override
    public SExpr getVariable(Parameter jmlBoundVariable) {
        ResolvedType rType = jmlBoundVariable.getType().resolve();
        return term.list(null, null, jmlBoundVariable.getNameAsString(), term.type(getType(rType)));
    }

    @Override
    public SExpr makeBoolean(boolean value) {
        return term.makeBoolean(value);
    }

    @Override
    public SmtType getType(ResolvedType type) {
        if (type.isPrimitive()) {
            ResolvedPrimitiveType rType = type.asPrimitive();
            return getPrimitiveType(rType);
        }

        if (type.isArray()) {
            ResolvedArrayType aType = type.asArrayType();
            SmtType cType = getType(aType.getComponentType());
            SmtType intType = getType(ResolvedPrimitiveType.INT);
            return new SmtType.Array(intType, cType);
        }

        if (type.isReferenceType()) {
            return SmtType.JAVA_OBJECT;
        }

        throw new RuntimeException("Unsupported type");
    }

    @Override
    public SExpr arrayLength(SExpr obj) {
        return term.list(ResolvedPrimitiveType.INT, SmtType.BV32, term.symbol("bv$length"), obj);
    }

    @Override
    public SExpr makeInt(long i) {
        return makeInt(BigInteger.valueOf(i));
    }

    public SmtType getPrimitiveType(ResolvedPrimitiveType rType) {
        switch (rType) {
            case BOOLEAN:
                return SmtType.BOOL;
            case BYTE:
                return SmtType.BV8;
            case SHORT:
                return SmtType.BV16;
            case CHAR:
                return SmtType.BV16;
            case INT:
                return SmtType.BV32;
            case LONG:
                return SmtType.BV64;
            case FLOAT:
                return SmtType.FP32;
            case DOUBLE:
                return SmtType.FP64;
        }
        return SmtType.BV8;
    }
}
