package com.github.javaparser.resolution.declarations;

import com.github.javaparser.ast.Node;

import java.util.Optional;

/**
 * A declaration that can be potentially associated with an AST node.
 * @param <N> type of AST Node that can be associated
 */
public interface AssociableToAST<N extends Node> {

    /**
     * If the declaration is associated to an AST node return it, otherwise it return empty.
     * Declaration based on source code have an AST node associated while others don't. Example
     * of other declarations are declarations coming from reflection or JARs.
     */
    default Optional<N> toAst() {
        throw new UnsupportedOperationException();
    }
}
