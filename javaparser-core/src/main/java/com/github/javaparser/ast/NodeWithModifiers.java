package com.github.javaparser.ast;

import java.util.EnumSet;

import com.github.javaparser.ast.body.Modifier;

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
    EnumSet<Modifier> getModifiers();
}