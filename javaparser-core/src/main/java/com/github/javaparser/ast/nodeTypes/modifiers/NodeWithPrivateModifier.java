package com.github.javaparser.ast.nodeTypes.modifiers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;

import static com.github.javaparser.ast.Modifier.*;

/**
 * A node that can be private.
 */
public interface NodeWithPrivateModifier<N extends Node> extends NodeWithModifiers<N> {
    default boolean isPrivate() {
        return getModifiers().contains(PRIVATE);
    }

    @SuppressWarnings("unchecked")
    default N setPrivate(boolean set) {
        return setModifier(PRIVATE, set);
    }
}
