package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;

public interface NodeWithArguments<N extends Node> {
    N setArgs(NodeList<Expression> args);

    NodeList<Expression> getArgs();

    default N addArgument(String arg) {
        addArgument(new NameExpr(arg));
        return (N) this;
    }

    default N addArgument(Expression arg) {
        getArgs().add(arg);
        return (N) this;
    }

}
