package com.github.jmlparser.smt;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.jmlparser.smt.model.SExpr;
import org.jetbrains.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
public class SMTFacade {
    public static SExpr toSmt(Expression expr, SmtQuery smtLog, boolean useInt) {
        JmlExpr2Smt visitor = new JmlExpr2Smt(
                smtLog, useInt ? new IntArithmeticTranslator(smtLog)
                : new BitVectorArithmeticTranslator(smtLog));
        return expr.accept(visitor, null);
    }
}
