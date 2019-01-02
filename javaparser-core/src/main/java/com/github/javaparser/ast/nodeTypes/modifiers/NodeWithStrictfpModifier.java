package com.github.javaparser.ast.nodeTypes.modifiers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;

import static com.github.javaparser.ast.Modifier.Keyword.STRICTFP;

/**
 * A node that can be strictfp.
 */
public interface NodeWithStrictfpModifier<N extends Node> extends NodeWithModifiers<N> {
    default boolean isStrictfp() {
        return hasModifier(STRICTFP);
    }

    @SuppressWarnings("unchecked")
    default N setStrictfp(boolean set) {
        return setModifier(STRICTFP, set);
    }
}
