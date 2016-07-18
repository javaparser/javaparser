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
 
package com.github.javaparser.ast.body;

import java.util.EnumSet;

import com.github.javaparser.ast.AccessSpecifier;

/**
 * Class to hold modifiers.<br>
 * The modifier constants declared here holds equivalent values to
 * {@link Modifier} constants.
 */
public final class ModifierSet {

    /* Definitions of the bits in the modifiers field.  */


	public static AccessSpecifier getAccessSpecifier(EnumSet<Modifier> modifiers) {
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

    public static EnumSet<Modifier> addModifier(EnumSet<Modifier> modifiers, Modifier mod) {
        if (modifiers == null)
            modifiers = EnumSet.of(mod);
        return modifiers;
    }

    public static boolean hasModifier(EnumSet<Modifier> modifiers, Modifier modifier) {
        if (modifiers == null)
            return false;
        return modifiers.contains(modifier);
    }

    public static boolean isAbstract(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.ABSTRACT);
    }

    public static boolean isFinal(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.FINAL);
    }

    public static boolean isNative(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.NATIVE);
    }

    public static boolean isPrivate(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.PRIVATE);
    }

    public static boolean isProtected(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.PROTECTED);
    }

    /**
     * Is the element accessible from within the package?
     * It is the level of access which is applied if no modifiers are chosen,
     * it is sometimes called "default".
     * @param modifiers indicator
     * @return true if modifier denotes package level access
     */
    public static boolean hasPackageLevelAccess(EnumSet<Modifier> modifiers) {
        return !isPublic(modifiers) && !isProtected(modifiers) && !isPrivate(modifiers);
    }

    public static boolean isPublic(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.PUBLIC);
    }

    public static boolean isStatic(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.STATIC);
    }

    public static boolean isStrictfp(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.STRICTFP);
    }

    public static boolean isSynchronized(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.SYNCHRONIZED);
    }

    public static boolean isTransient(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.TRANSIENT);
    }

    public static boolean isVolatile(EnumSet<Modifier> modifiers) {
        return hasModifier(modifiers, Modifier.VOLATILE);
    }

    /**
     * Removes the given modifier.
     * @param modifiers existing modifiers
     * @param mod modifier to be removed
     * @return result for removing modifier
     */
    public static void removeModifier(EnumSet<Modifier> modifiers, Modifier mod) {
        modifiers.remove(mod);
    }

    private ModifierSet() {
    }
}