package com.github.jmlparser.wd;

import com.github.javaparser.ast.JmlBoundVariable;
import com.github.javaparser.ast.expr.*;
import org.sosy_lab.java_smt.api.*;

import java.math.BigInteger;

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
public class BitVectorTranslator implements Translator {
    private final SolverContext context;
    private final BooleanFormulaManager boolmgr;
    private final BitvectorFormulaManager bmgr;
    private int cnt = 0;

    public BitVectorTranslator(SolverContext context) {
        this.context = context;
        this.boolmgr = context.getFormulaManager().getBooleanFormulaManager();
        this.bmgr = context.getFormulaManager().getBitvectorFormulaManager();
    }

    @Override
    public Formula binary(BinaryExpr.Operator operator, Formula left, Formula right) {
        switch (operator) {
            case IMPLICATION:
                return boolmgr.implication((BooleanFormula) left, (BooleanFormula) right);
            case SUBTYPE:
                break;
            case RANGE:
                break;
            case SUB_LOCK:
                break;
            case SUB_LOCKE:
                break;
            case RIMPLICATION:
                return boolmgr.implication((BooleanFormula) right, (BooleanFormula) left);
            case EQUIVALENCE:
                return boolmgr.equivalence((BooleanFormula) left, (BooleanFormula) right);
            case ANTIVALENCE:
                return boolmgr.not(boolmgr.equivalence((BooleanFormula) left, (BooleanFormula) right));
            case OR:
                return boolmgr.or((BooleanFormula) left, (BooleanFormula) right);
            case AND:
                return boolmgr.and((BooleanFormula) left, (BooleanFormula) right);
            case BINARY_OR:
                return bmgr.or((BitvectorFormula) left, (BitvectorFormula) right);
            case BINARY_AND:
                return bmgr.and((BitvectorFormula) left, (BitvectorFormula) right);
            case XOR:
                return bmgr.xor((BitvectorFormula) left, (BitvectorFormula) right);
            case EQUALS:
                return bmgr.equal((BitvectorFormula) left, (BitvectorFormula) right);
            case NOT_EQUALS:
                return boolmgr.not(bmgr.equal((BitvectorFormula) left, (BitvectorFormula) right));
            case LESS:
                return bmgr.lessThan((BitvectorFormula) left, (BitvectorFormula) right, true);
            case GREATER:
                return bmgr.greaterThan((BitvectorFormula) left, (BitvectorFormula) right, true);
            case LESS_EQUALS:
                return bmgr.lessOrEquals((BitvectorFormula) left, (BitvectorFormula) right, true);
            case GREATER_EQUALS:
                return bmgr.greaterOrEquals((BitvectorFormula) left, (BitvectorFormula) right, true);
            case LEFT_SHIFT:
                return bmgr.shiftLeft((BitvectorFormula) left, (BitvectorFormula) right);
            case SIGNED_RIGHT_SHIFT:
                return bmgr.shiftRight((BitvectorFormula) left, (BitvectorFormula) right, true);
            case UNSIGNED_RIGHT_SHIFT:
                return bmgr.shiftRight((BitvectorFormula) left, (BitvectorFormula) right, true);
            case PLUS:
                return bmgr.add((BitvectorFormula) left, (BitvectorFormula) right);
            case MINUS:
                return bmgr.subtract((BitvectorFormula) left, (BitvectorFormula) right);
            case MULTIPLY:
                return bmgr.multiply((BitvectorFormula) left, (BitvectorFormula) right);
            case DIVIDE:
                return bmgr.divide((BitvectorFormula) left, (BitvectorFormula) right, true);
            case REMAINDER:
                return bmgr.modulo((BitvectorFormula) left, (BitvectorFormula) right, true);

        }
        return null;
    }

    @Override
    public Formula makeChar(CharLiteralExpr n) {
        return bmgr.makeBitvector(16, n.getValue().charAt(0));
    }

    @Override
    public Formula unary(UnaryExpr.Operator operator, Formula accept) {
        switch (operator) {
            case PLUS:
            case POSTFIX_INCREMENT:
            case POSTFIX_DECREMENT:
                return accept;
            case MINUS:
                return bmgr.negate((BitvectorFormula) accept);
            case PREFIX_INCREMENT:
                return bmgr.add((BitvectorFormula) accept, bmgr.makeBitvector(32, 1));
            case PREFIX_DECREMENT:
                return bmgr.subtract((BitvectorFormula) accept, bmgr.makeBitvector(32, 1));
            case LOGICAL_COMPLEMENT:
                return boolmgr.not((BooleanFormula) accept);
            case BITWISE_COMPLEMENT:
                return bmgr.not((BitvectorFormula) accept);
        }
        return accept;
    }

    @Override
    public Formula makeLong(LongLiteralExpr n) {
        return bmgr.makeBitvector(64, n.asLong());
    }

    @Override
    public Formula makeInt(IntegerLiteralExpr n) {
        return bmgr.makeBitvector(32, n.asInt());
    }

    @Override
    public Formula makeInt(BigInteger i) {
        return bmgr.makeBitvector(32, i);
    }

    @Override
    public Formula makeIntVar() {
        return bmgr.makeVariable(32, "__RAND_" + (++cnt));
    }

    @Override
    public Formula getVariable0(JmlBoundVariable jmlBoundVariable) {
        return null;
    }
}
