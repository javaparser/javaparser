package com.github.javaparser.ast.nodeTypes.modifiers;

import com.github.javaparser.ast.Node;

/**
 * A node that can be public, protected, and/or private.
 */
public interface NodeWithAccessModifiers<N extends Node> extends NodeWithPublicModifier<N>, NodeWithPrivateModifier<N>, NodeWithProtectedModifier<N> {
}
