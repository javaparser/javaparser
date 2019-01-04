package com.github.javaparser.ast.nodeTypes.modifiers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;

import static com.github.javaparser.ast.Modifier.Keyword.ABSTRACT;

/**
 * A node that can be abstract.
 */
public interface NodeWithAbstractModifier<N extends Node> extends NodeWithModifiers<N> {
    default boolean isAbstract() {
        return hasModifier(ABSTRACT);
    }

    @SuppressWarnings("unchecked")
    default N setAbstract(boolean set) {
        return setModifier(ABSTRACT, set);
    }
}
