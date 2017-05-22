package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;

public interface NodeWithCondition<N extends Node> {
    Expression getCondition();

    N setCondition(Expression condition);
}
