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
import java.util.*;

/**
 * Class to hold modifiers.<br>
 * The modifier constants declared here holds equivalent values to
 * {@link Modifier} constants.
 */
public final class ModifierSet {

    /* Definitions of the bits in the modifiers field.  */
    
    private static Map<javax.lang.model.element.Modifier, Integer> ENUM_TO_INT = new HashMap<javax.lang.model.element.Modifier, Integer>();
    
    static {
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.ABSTRACT, Modifier.ABSTRACT);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.FINAL, Modifier.FINAL);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.NATIVE, Modifier.NATIVE);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.PRIVATE, Modifier.PRIVATE);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.PROTECTED, Modifier.PROTECTED);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.PUBLIC, Modifier.PUBLIC);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.STATIC, Modifier.STATIC);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.STRICTFP, Modifier.STRICT);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.SYNCHRONIZED, Modifier.SYNCHRONIZED);
        ENUM_TO_INT.put(javax.lang.model.element.Modifier.TRANSIENT, Modifier.TRANSIENT);
    }

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

    /** @deprecated use {@link #hasModifier(NodeWithModifiers, javax.lang.model.element.Modifier)} (...)} instead */
    @Deprecated
    public static boolean hasModifier(int modifiers, int modifier) {
        return (modifiers & modifier) != 0;
    }

    public static boolean hasModifier(NodeWithModifiers node, javax.lang.model.element.Modifier modifier) {
        return node.getModifiersSet().contains(modifier);
    }

    /** @deprecated use {@link #isAbstract(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isAbstract(int modifiers) {
        return (modifiers & ABSTRACT) != 0;
    }

    public static boolean isAbstract(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.ABSTRACT);
    }

    /** @deprecated use {@link #isFinal(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isFinal(int modifiers) {
        return (modifiers & FINAL) != 0;
    }

    public static boolean isFinal(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.FINAL);
    }

    /** @deprecated use {@link #isNative(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isNative(int modifiers) {
        return (modifiers & NATIVE) != 0;
    }

    public static boolean isNative(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.NATIVE);
    }

    /** @deprecated use {@link #isPrivate(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isPrivate(int modifiers) {
        return (modifiers & PRIVATE) != 0;
    }

    public static boolean isPrivate(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.PRIVATE);
    }

    /** @deprecated use {@link #isProtected(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isProtected(int modifiers) {
        return (modifiers & PROTECTED) != 0;
    }

    public static boolean isProtected(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.PROTECTED);
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
        return hasModifier(node, javax.lang.model.element.Modifier.PUBLIC);
    }

    /** @deprecated use {@link #isStatic(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isStatic(int modifiers) {
        return (modifiers & STATIC) != 0;
    }

    public static boolean isStatic(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.STATIC);
    }

    /** @deprecated use {@link #isStrictfp(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isStrictfp(int modifiers) {
        return (modifiers & STRICTFP) != 0;
    }

    public static boolean isStrictfp(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.STRICTFP);
    }

    /** @deprecated use {@link #isSynchronized(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isSynchronized(int modifiers) {
        return (modifiers & SYNCHRONIZED) != 0;
    }

    public static boolean isSynchronized(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.SYNCHRONIZED);
    }

    /** @deprecated use {@link #isTransient(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isTransient(int modifiers) {
        return (modifiers & TRANSIENT) != 0;
    }

    public static boolean isTransient(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.TRANSIENT);
    }

    /** @deprecated use {@link #isVolatile(NodeWithModifiers)} (...)} instead */
    @Deprecated
    public static boolean isVolatile(int modifiers) {
        return (modifiers & VOLATILE) != 0;
    }

    public static boolean isVolatile(NodeWithModifiers node) {
        return hasModifier(node, javax.lang.model.element.Modifier.VOLATILE);
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

    public static Set<javax.lang.model.element.Modifier> toSet(int modifiersAsInt) {
        Set<javax.lang.model.element.Modifier> modifiersAsSet = EnumSet.noneOf(javax.lang.model.element.Modifier.class);
        for (javax.lang.model.element.Modifier modifier : ENUM_TO_INT.keySet()) {
            if (hasModifier(modifiersAsInt, ENUM_TO_INT.get(modifier))){
                modifiersAsSet.add(modifier);
            }
        }
        return modifiersAsSet;
    }

    public static int toInt(Set<javax.lang.model.element.Modifier> modifiersAsSet) {
        int modifiersAsInt = 0;
        for (javax.lang.model.element.Modifier modifier : ENUM_TO_INT.keySet()) {
            if (modifiersAsSet.contains(modifier)){
                modifiersAsInt |= ENUM_TO_INT.get(modifier);
            }
        }
        return modifiersAsInt;
    }
}