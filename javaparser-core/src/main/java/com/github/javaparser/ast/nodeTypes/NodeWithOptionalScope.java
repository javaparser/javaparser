package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;

import java.util.Optional;

/**
 * Represents a node which can have a scope expression eg. method calls or
 * field accesses (object.method(), object.field).
 */
public interface NodeWithOptionalScope<N extends Node> {

    Optional<Expression> getScope();

    N setScope(final Expression scope);
}
