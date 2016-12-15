package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;

public interface NodeWithArguments<N extends Node> {
    N setArguments(NodeList<Expression> arguments);

    NodeList<Expression> getArguments();

    default Expression getArgument(int i) {
        return getArguments().get(i);
    }

    @SuppressWarnings("unchecked")
    default N addArgument(String arg) {
        addArgument(new NameExpr(arg));
        return (N) this;
    }

    @SuppressWarnings("unchecked")
    default N addArgument(Expression arg) {
        getArguments().add(arg);
        return (N) this;
    }

}
