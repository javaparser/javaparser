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
        Expression r;
        if (n.getExpressions().isEmpty()) {
            r = new BooleanLiteralExpr(true);
        } else if (n.getExpressions().size() == 1) {
            r = n.getExpressions().get(0);
        } else {
            Expression e = null;
            for (int i = 0; i < n.getExpressions().size() - 1; i++) {
                BinaryExpr cmp = new BinaryExpr(
                        n.getExpressions().get(i).clone(),
                        n.getExpressions().get(i + 1).clone(),
                        n.getOperators().get(i));
                e = e == null ? cmp : new BinaryExpr(e, cmp, BinaryExpr.Operator.AND);
            }
            r = e;
        }
        r.setParentNode(n.getParentNode().orElse(null));
        return r;
    }
}
