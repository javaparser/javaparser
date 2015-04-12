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
import com.github.javaparser.ast.Modifiers;
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
    
    private static Map<Modifiers.Modifier, Integer> ENUM_TO_INT = new HashMap<Modifiers.Modifier, Integer>();
    
    static {
        ENUM_TO_INT.put(Modifiers.Modifier.ABSTRACT, Modifier.ABSTRACT);
        ENUM_TO_INT.put(Modifiers.Modifier.FINAL, Modifier.FINAL);
        ENUM_TO_INT.put(Modifiers.Modifier.NATIVE, Modifier.NATIVE);
        ENUM_TO_INT.put(Modifiers.Modifier.PRIVATE, Modifier.PRIVATE);
        ENUM_TO_INT.put(Modifiers.Modifier.PROTECTED, Modifier.PROTECTED);
        ENUM_TO_INT.put(Modifiers.Modifier.PUBLIC, Modifier.PUBLIC);
        ENUM_TO_INT.put(Modifiers.Modifier.STATIC, Modifier.STATIC);
        ENUM_TO_INT.put(Modifiers.Modifier.STRICTFP, Modifier.STRICT);
        ENUM_TO_INT.put(Modifiers.Modifier.SYNCHRONIZED, Modifier.SYNCHRONIZED);
        ENUM_TO_INT.put(Modifiers.Modifier.TRANSIENT, Modifier.TRANSIENT);
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

    public static AccessSpecifier getAccessSpecifier(NodeWithModifiers modifiers) {
        return modifiers.getModifiersSet().getAccessSpecifier();
    }

    public static int addModifier(int modifiers, int mod) {
        return modifiers | mod;
    }

    @Deprecated
    public static boolean hasModifier(int modifiers, int modifier) {
        return (modifiers & modifier) != 0;
    }

    @Deprecated
    public static boolean isAbstract(int modifiers) {
        return (modifiers & ABSTRACT) != 0;
    }

    @Deprecated
    public static boolean isFinal(int modifiers) {
        return (modifiers & FINAL) != 0;
    }

    @Deprecated
    public static boolean isNative(int modifiers) {
        return (modifiers & NATIVE) != 0;
    }

    @Deprecated
    public static boolean isPrivate(int modifiers) {
        return (modifiers & PRIVATE) != 0;
    }

    @Deprecated
    public static boolean isProtected(int modifiers) {
        return (modifiers & PROTECTED) != 0;
    }

    /**
     * Is the element accessible from within the package?
     * It is the level of access which is applied if no modifiers are chosen,
     * it is sometimes called "default".
     * @param modifiers indicator
     * @return true if modifier denotes package level access
     */
    @Deprecated
    public static boolean hasPackageLevelAccess(int modifiers) {
        return !isPublic(modifiers) && !isProtected(modifiers) && !isPrivate(modifiers);
    }

    @Deprecated
    public static boolean isPublic(int modifiers) {
        return (modifiers & PUBLIC) != 0;
    }

    @Deprecated
    public static boolean isStatic(int modifiers) {
        return (modifiers & STATIC) != 0;
    }

    @Deprecated
    public static boolean isStrictfp(int modifiers) {
        return (modifiers & STRICTFP) != 0;
    }

    @Deprecated
    public static boolean isSynchronized(int modifiers) {
        return (modifiers & SYNCHRONIZED) != 0;
    }

    @Deprecated
    public static boolean isTransient(int modifiers) {
        return (modifiers & TRANSIENT) != 0;
    }


    @Deprecated
    public static boolean isVolatile(int modifiers) {
        return (modifiers & VOLATILE) != 0;
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

    public static Modifiers toSet(int modifiersAsInt) {
        Modifiers modifiersAsSet = new Modifiers();
        for (Modifiers.Modifier modifier : ENUM_TO_INT.keySet()) {
            if (hasModifier(modifiersAsInt, ENUM_TO_INT.get(modifier))){
                modifiersAsSet = modifiersAsSet.set(modifier);
            }
        }
        return modifiersAsSet;
    }

    public static int toInt(Modifiers modifiersAsSet) {
        int modifiersAsInt = 0;
        for (Modifiers.Modifier modifier : ENUM_TO_INT.keySet()) {
            if (modifiersAsSet.has(modifier)){
                modifiersAsInt |= ENUM_TO_INT.get(modifier);
            }
        }
        return modifiersAsInt;
    }
}