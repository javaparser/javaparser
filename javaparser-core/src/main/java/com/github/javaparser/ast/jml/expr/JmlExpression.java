package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.expr.Expression;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/6/26)
 */
public abstract class JmlExpression extends Expression implements Jmlish {
    public JmlExpression() {
        super();
    }

    public JmlExpression(TokenRange tokenRange) {
        super(tokenRange);
    }
}
