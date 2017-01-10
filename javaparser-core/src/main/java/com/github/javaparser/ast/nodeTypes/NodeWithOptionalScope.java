package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;

import java.util.Optional;

/**
 * @author Artur Bosch
 */
public interface NodeWithOptionalScope<N extends Node> {

	Optional<Expression> getScope();

	N setScope(final Expression scope);
}
