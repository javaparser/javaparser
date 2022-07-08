package com.github.jmlparser.utils;

import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr;

/**
 * @author Alexander Weigl
 * @version 1 (02.07.22)
 */
public class JMLUtils {
    public static Expression unroll(JmlMultiCompareExpr n) {
        if (n.getExpressions().isEmpty()) {
            return new BooleanLiteralExpr(true);
        } else if (n.getExpressions().size() == 1) {
            return n.getExpressions().get(0);
        } else {
            Expression e = new BooleanLiteralExpr(true);
            for (int i = 0; i < n.getExpressions().size() - 1; i++) {
                BinaryExpr cmp = new BinaryExpr(
                        n.getExpressions().get(i),
                        n.getExpressions().get(i + 1),
                        n.getOperators().get(i));
                e = new BinaryExpr(e, cmp, BinaryExpr.Operator.AND);
            }
            return e;
        }
    }
}
