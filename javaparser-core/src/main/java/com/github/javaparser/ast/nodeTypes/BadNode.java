package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;

/**
 * A node with parse problems.
 * These nodes are stored as "only text".
 */
public interface BadNode<N extends Node> {
    String getSourceText();

    N setSourceText(String sourceText);
}
