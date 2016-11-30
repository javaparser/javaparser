package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclaratorId;

public interface NodeWithVariableDeclaratorId<N extends Node> {
    VariableDeclaratorId getIdentifier();

    N setIdentifier(VariableDeclaratorId identifier);

    default String getIdentifierAsString() {
        return getIdentifier().getNameAsString();
    }

    default N setIdentifier(String identifier) {
        getIdentifier().setName(identifier);
        return (N) this;
    }
}
