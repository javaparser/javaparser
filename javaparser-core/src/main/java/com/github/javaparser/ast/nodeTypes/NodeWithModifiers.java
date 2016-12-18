/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

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
     * @return modifiers
     * @see Modifier
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