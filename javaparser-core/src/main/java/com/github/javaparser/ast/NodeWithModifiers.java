package com.github.javaparser.ast;

import com.github.javaparser.ast.body.ModifierSet;

/**
 * A Node with Modifiers.
 */
public interface NodeWithModifiers<T> {
    /**
     * Return the modifiers of this variable declaration.
     *
     * @see ModifierSet
     * @return modifiers
     */
    int getModifiers();

    default boolean isStatic() {
        return ModifierSet.isStatic(getModifiers());
    }

    default boolean isAbstract() {
        return ModifierSet.isAbstract(getModifiers());
    }

    default boolean isFinal() {
        return ModifierSet.isFinal(getModifiers());
    }

    default boolean isNative() {
        return ModifierSet.isNative(getModifiers());
    }

    default boolean isPrivate() {
        return ModifierSet.isPrivate(getModifiers());
    }

    default boolean isProtected() {
        return ModifierSet.isProtected(getModifiers());
    }

    default boolean isPublic() {
        return ModifierSet.isPublic(getModifiers());
    }

    default boolean isStrictfp() {
        return ModifierSet.isStrictfp(getModifiers());
    }

    default boolean isSynchronized() {
        return ModifierSet.isSynchronized(getModifiers());
    }

    default boolean isTransient() {
        return ModifierSet.isTransient(getModifiers());
    }

    default boolean isVolatile() {
        return ModifierSet.isVolatile(getModifiers());
    }
}