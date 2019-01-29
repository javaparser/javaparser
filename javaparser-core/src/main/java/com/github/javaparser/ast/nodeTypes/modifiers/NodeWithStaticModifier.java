package com.github.javaparser.ast.nodeTypes.modifiers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;

import static com.github.javaparser.ast.Modifier.Keyword.STATIC;

/**
 * A node that can be static.
 */
public interface NodeWithStaticModifier<N extends Node> extends NodeWithModifiers<N> {

    default boolean isStatic() {
        return hasModifier(STATIC);
    }

    @SuppressWarnings("unchecked")
    default N setStatic(boolean set) {
        return setModifier(STATIC, set);
    }

}
