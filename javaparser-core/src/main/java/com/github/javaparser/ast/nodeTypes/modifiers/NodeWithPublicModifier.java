package com.github.javaparser.ast.nodeTypes.modifiers;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;

import static com.github.javaparser.ast.Modifier.Keyword.PUBLIC;

/**
 * A node that can be public.
 */
public interface NodeWithPublicModifier<N extends Node> extends NodeWithModifiers<N> {
    default boolean isPublic() {
        return hasModifier(PUBLIC);
    }

    @SuppressWarnings("unchecked")
    default N setPublic(boolean set) {
        return setModifier(PUBLIC, set);
    }

}
