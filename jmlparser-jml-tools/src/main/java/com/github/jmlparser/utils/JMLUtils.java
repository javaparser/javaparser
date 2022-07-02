package com.github.jmlparser.utils;

import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause;
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr;

/**
 * @author Alexander Weigl
 * @version 1 (02.07.22)
 */
public class JMLUtils {
    public static Expression unroll(JmlMultiCompareExpr n) {
        if (n.getExprs().isEmpty()) {
            return new BooleanLiteralExpr(true);
        } else if (n.getExprs().size() == 1) {
            return n.getExprs().get(0);
        } else {
            Expression e = new BooleanLiteralExpr(true);
            for (int i = 0; i < n.getExprs().size() - 1; i++) {
                BinaryExpr cmp = new BinaryExpr(
                        n.getExprs().get(i),
                        n.getExprs().get(i + 1),
                        n.getOperators().get(i));
                e = new BinaryExpr(e, cmp, BinaryExpr.Operator.AND);
            }
            return e;
        }
    }
}
