package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;

public interface NodeWithArguments<T> {
    T setArgs(NodeList<Expression> args);

    NodeList<Expression> getArgs();

    default T addArgument(String arg) {
        addArgument(new NameExpr(arg));
        return (T) this;
    }

    default T addArgument(Expression arg) {
        getArgs().add(arg);
        return (T) this;
    }

}
