package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.stream.Collectors;

/**
 * A Node with Modifiers.
 */
public interface NodeWithModifiers<N extends Node> {
    /**
     * Return the modifiers of this variable declaration.
     *
     * @see Modifier
     * @return modifiers
     */
    EnumSet<Modifier> getModifiers();

    N setModifiers(EnumSet<Modifier> modifiers);

    @SuppressWarnings("unchecked")
    default N addModifier(Modifier... modifiers) {
        getModifiers().addAll(Arrays.stream(modifiers)
                .collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))));
        return (N) this;
    }

    default boolean isStatic() {
        return getModifiers().contains(Modifier.STATIC);
    }

    default boolean isAbstract() {
        return getModifiers().contains(Modifier.ABSTRACT);
    }

    default boolean isFinal() {
        return getModifiers().contains(Modifier.FINAL);
    }

    default boolean isNative() {
        return getModifiers().contains(Modifier.NATIVE);
    }

    default boolean isPrivate() {
        return getModifiers().contains(Modifier.PRIVATE);
    }

    default boolean isProtected() {
        return getModifiers().contains(Modifier.PROTECTED);
    }

    default boolean isPublic() {
        return getModifiers().contains(Modifier.PUBLIC);
    }

    default boolean isStrictfp() {
        return getModifiers().contains(Modifier.STRICTFP);
    }

    default boolean isSynchronized() {
        return getModifiers().contains(Modifier.SYNCHRONIZED);
    }

    default boolean isTransient() {
        return getModifiers().contains(Modifier.TRANSIENT);
    }

    default boolean isVolatile() {
        return getModifiers().contains(Modifier.VOLATILE);
    }
}