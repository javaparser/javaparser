package com.github.javaparser.ast;

import com.github.javaparser.ast.body.ModifierSet;

/**
 * A Node with Modifiers.
 */
public interface NodeWithModifiers {
	/**
	 * Return the modifiers of this variable declaration.
	 *
	 * @see ModifierSet
	 * @return modifiers
	 */
	int getModifiers();
}