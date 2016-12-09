package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;

public interface NodeWithExpression<N extends Node> {
    Expression getExpression();

    N setExpression(Expression expression);
}
