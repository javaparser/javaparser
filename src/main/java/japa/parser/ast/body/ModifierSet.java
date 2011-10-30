/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
package japa.parser.ast.body;

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

    /**
     * Adds the given modifier.
     */
    public static int addModifier(int modifiers, int mod) {
        return modifiers | mod;
    }

    public static boolean hasModifier(int modifiers, int modifier) {
        return (modifiers & modifier) != 0;
    }

    public static boolean isAbstract(int modifiers) {
        return (modifiers & ABSTRACT) != 0;
    }

    public static boolean isFinal(int modifiers) {
        return (modifiers & FINAL) != 0;
    }

    public static boolean isNative(int modifiers) {
        return (modifiers & NATIVE) != 0;
    }

    public static boolean isPrivate(int modifiers) {
        return (modifiers & PRIVATE) != 0;
    }

    public static boolean isProtected(int modifiers) {
        return (modifiers & PROTECTED) != 0;
    }

    /**
     * A set of accessors that indicate whether the specified modifier is in the
     * set.
     */

    public static boolean isPublic(int modifiers) {
        return (modifiers & PUBLIC) != 0;
    }

    public static boolean isStatic(int modifiers) {
        return (modifiers & STATIC) != 0;
    }

    public static boolean isStrictfp(int modifiers) {
        return (modifiers & STRICTFP) != 0;
    }

    public static boolean isSynchronized(int modifiers) {
        return (modifiers & SYNCHRONIZED) != 0;
    }

    public static boolean isTransient(int modifiers) {
        return (modifiers & TRANSIENT) != 0;
    }

    public static boolean isVolatile(int modifiers) {
        return (modifiers & VOLATILE) != 0;
    }

    /**
     * Removes the given modifier.
     */
    public static int removeModifier(int modifiers, int mod) {
        return modifiers & ~mod;
    }

    private ModifierSet() {
    }
}