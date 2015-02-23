/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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
 
package com.github.javaparser.ast.body;

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.NodeWithModifiers;

import java.lang.reflect.Modifier;

/**
 * Class to hold modifiers.<br>
 * The modifier constants declared here holds equivalent values to
 * {@link Modifier} constants.
 */
public final class ModifierSet {

    /* Definitions of the bits in the modifiers field.  */

    public static final int PUBLIC = Modifier.PUBLIC;

    public static final int PRIVATE = Modifier.PRIVATE;

    public static final int PROTECTED = Modifier.PROTECTED;

    public static final int STATIC = Modifier.STATIC;

    public static final int FINAL = Modifier.FINAL;

    public static final int SYNCHRONIZED = Modifier.SYNCHRONIZED;

    public static final int VOLATILE = Modifier.VOLATILE;

    public static final int TRANSIENT = Modifier.TRANSIENT;

    public static final int NATIVE = Modifier.NATIVE;

    public static final int ABSTRACT = Modifier.ABSTRACT;

    public static final int STRICTFP = Modifier.STRICT;

    @Deprecated
    public static AccessSpecifier getAccessSpecifier(int modifiers) {
        if (isPublic(modifiers)){
            return AccessSpecifier.PUBLIC;
        } else if (isProtected(modifiers)){
            return AccessSpecifier.PROTECTED;
        } else if (isPrivate(modifiers)){
            return AccessSpecifier.PRIVATE;
        } else {
            return AccessSpecifier.DEFAULT;
        }
    }

    public static AccessSpecifier getAccessSpecifier(NodeWithModifiers node) {
        if (isPublic(node)){
            return AccessSpecifier.PUBLIC;
        } else if (isProtected(node)){
            return AccessSpecifier.PROTECTED;
        } else if (isPrivate(node)){
            return AccessSpecifier.PRIVATE;
        } else {
            return AccessSpecifier.DEFAULT;
        }
    }

    public static int addModifier(int modifiers, int mod) {
        return modifiers | mod;
    }

    /** @deprecated use {@link #hasModifier(NodeWithModifiers, int)} (...)} instead */
    @Deprecated
    public static boolean hasModifier(int modifiers, int modifier) {
        return (modifiers & modifier) != 0;
    }

    public static boolean hasModifier(NodeWithModifiers node, int modifier) {
        return (node.getModifiers() & modifier) != 0;
    }

    /** @deprecated use {@link #isAbstract(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isAbstract(int modifiers) {
        return (modifiers & ABSTRACT) != 0;
    }

    public static boolean isAbstract(NodeWithModifiers node) {
        return (node.getModifiers() & ABSTRACT) != 0;
    }

    /** @deprecated use {@link #isFinal(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isFinal(int modifiers) {
        return (modifiers & FINAL) != 0;
    }

    public static boolean isFinal(NodeWithModifiers node) {
        return (node.getModifiers() & FINAL) != 0;
    }

    /** @deprecated use {@link #isNative(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isNative(int modifiers) {
        return (modifiers & NATIVE) != 0;
    }

    public static boolean isNative(NodeWithModifiers node) {
        return (node.getModifiers() & NATIVE) != 0;
    }

    /** @deprecated use {@link #isPrivate(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isPrivate(int modifiers) {
        return (modifiers & PRIVATE) != 0;
    }

    public static boolean isPrivate(NodeWithModifiers node) {
        return (node.getModifiers() & PRIVATE) != 0;
    }

    /** @deprecated use {@link #isProtected(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isProtected(int modifiers) {
        return (modifiers & PROTECTED) != 0;
    }

    public static boolean isProtected(NodeWithModifiers node) {
        return (node.getModifiers() & PROTECTED) != 0;
    }

    /**
     * Is the element accessible from within the package?
     * It is the level of access which is applied if no modifiers are chosen,
     * it is sometimes called "default".
     * @param modifiers indicator
     * @return true if modifier denotes package level access
     * @deprecated use {@link #hasPackageLevelAccess(NodeWithModifiers)} (...)} instead
     */
    @Deprecated
    public static boolean hasPackageLevelAccess(int modifiers) {
        return !isPublic(modifiers) && !isProtected(modifiers) && !isPrivate(modifiers);
    }

    /**
     * Is the element accessible from within the package?
     * It is the level of access which is applied if no modifiers are chosen,
     * it is sometimes called "default".
     * @return true if modifier denotes package level access
     */
    public static boolean hasPackageLevelAccess(NodeWithModifiers node) {
        return !isPublic(node) && !isProtected(node) && !isPrivate(node);
    }

    /** @deprecated use {@link #isPublic(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isPublic(int modifiers) {
        return (modifiers & PUBLIC) != 0;
    }

    public static boolean isPublic(NodeWithModifiers node) {
        return (node.getModifiers() & PUBLIC) != 0;
    }

    /** @deprecated use {@link #isStatic(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isStatic(int modifiers) {
        return (modifiers & STATIC) != 0;
    }

    public static boolean isStatic(NodeWithModifiers node) {
        return (node.getModifiers() & STATIC) != 0;
    }

    /** @deprecated use {@link #isStrictfp(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isStrictfp(int modifiers) {
        return (modifiers & STRICTFP) != 0;
    }

    public static boolean isStrictfp(NodeWithModifiers node) {
        return (node.getModifiers() & STRICTFP) != 0;
    }

    /** @deprecated use {@link #isSynchronized(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isSynchronized(int modifiers) {
        return (modifiers & SYNCHRONIZED) != 0;
    }

    public static boolean isSynchronized(NodeWithModifiers node) {
        return (node.getModifiers() & SYNCHRONIZED) != 0;
    }

    /** @deprecated use {@link #isTransient(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isTransient(int modifiers) {
        return (modifiers & TRANSIENT) != 0;
    }

    public static boolean isTransient(NodeWithModifiers node) {
        return (node.getModifiers() & TRANSIENT) != 0;
    }

    /** @deprecated use {@link #isVolatile(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isVolatile(int modifiers) {
        return (modifiers & VOLATILE) != 0;
    }

    public static boolean isVolatile(NodeWithModifiers node) {
        return (node.getModifiers() & VOLATILE) != 0;
    }

    /**
     * Removes the given modifier.
     * @param modifiers existing modifiers
     * @param mod modifier to be removed
     * @return result for removing modifier
     */
    public static int removeModifier(int modifiers, int mod) {
        return modifiers & ~mod;
    }

    private ModifierSet() {
    }
}