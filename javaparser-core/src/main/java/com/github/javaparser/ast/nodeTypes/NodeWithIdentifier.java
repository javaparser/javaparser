package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;

public interface NodeWithIdentifier<N extends Node> {
    String getIdentifier();
    
    N setIdentifier(String identifier);

    default String getId() {
        return getIdentifier();
    }

    default N setId(String identifier) {
        return setIdentifier(identifier);
    }
}
