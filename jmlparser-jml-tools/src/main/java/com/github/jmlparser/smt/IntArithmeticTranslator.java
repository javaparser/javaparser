package com.github.jmlparser.smt;

import com.github.javaparser.ast.expr.CharLiteralExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.jmlparser.smt.model.SExpr;
import com.github.jmlparser.smt.model.SmtType;

import java.math.BigInteger;

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
public class IntArithmeticTranslator extends BitVectorArithmeticTranslator {
    private final SmtTermFactory term = SmtTermFactory.INSTANCE;

    public IntArithmeticTranslator(SmtQuery smtLog) {
        super((smtLog));
    }

    @Override
    public SExpr makeChar(CharLiteralExpr n) {
        return term.makeInt("" + (int) n.asChar());
    }

    @Override
    public SExpr makeLong(LongLiteralExpr n) {
        return term.makeInt("" + n.getValue());

    }

    @Override
    public SExpr makeInt(IntegerLiteralExpr n) {
        return term.makeInt("" + n.getValue());
    }

    @Override
    public SExpr makeInt(BigInteger i) {
        return term.makeInt(i.toString());
    }

    @Override
    public SExpr makeIntVar() {
        String name = "__RAND_" + (++cnt);
        smtLog.declareConst(name, SmtType.BV32);
        return term.symbol(name);
    }

    @Override
    public SmtType getPrimitiveType(ResolvedPrimitiveType rType) {
        switch (rType) {
            case FLOAT:
            case DOUBLE:
                return SmtType.REAL;
        }
        return SmtType.INT;
    }

    @Override
    public SExpr arrayLength(SExpr obj) {
        return term.list(ResolvedPrimitiveType.INT, SmtType.INT, term.symbol("int$length"), obj);
    }
}
