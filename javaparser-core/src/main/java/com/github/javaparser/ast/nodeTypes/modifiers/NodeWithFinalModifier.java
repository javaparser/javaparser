package com.github.javaparser.ast.nodeTypes.modifiers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;

import static com.github.javaparser.ast.Modifier.Keyword.FINAL;

/**
 * A node that can be final.
 */
public interface NodeWithFinalModifier<N extends Node> extends NodeWithModifiers<N> {
    default boolean isFinal() {
        return hasModifier(FINAL);
    }

    @SuppressWarnings("unchecked")
    default N setFinal(boolean set) {
        return setModifier(FINAL, set);
    }
}
