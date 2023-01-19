/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
package com.github.javaparser.quality;

public final class Preconditions {

    private Preconditions() {
        // This constructor hide the public one.
    }

    /**
     * Ensures the truth of an expression involving one or more parameters to the calling method.
     *
     * @param expression 	a boolean expression.
     * @param message		the exception message to use if the check fails;
     *                      will be converted to a string using String.valueOf(Object)
     *
     * @throws IllegalArgumentException if expression is false.
     */
    public static void checkArgument(boolean expression, Object message) {
        if (!expression) {
            throw new IllegalArgumentException(String.valueOf(message));
        }
    }

    /**
     * Ensures the truth of an expression involving one or more parameters to the calling method.
     *
     * @param expression 	a boolean expression.
     *
     * @throws IllegalArgumentException if expression is false.
     */
    public static void checkArgument(boolean expression) {
        checkArgument(expression, "Invalid argument provided.");
    }

    /**
     * Ensures that an object reference passed as a parameter to the calling method is not null.
     *
     * @param reference 	an object reference.
     * @param message		the exception message to use if the check fails;
     *                      will be converted to a string using String.valueOf(Object)
     *
     * @throws IllegalArgumentException if reference is {@code null}.
     */
    public static void checkNotNull(Object reference, Object message) {
        checkArgument(reference != null, message);
    }

    /**
     * Ensures that an object reference passed as a parameter to the calling method is not null.
     *
     * @param reference 	an object reference.
     *
     * @throws IllegalArgumentException if reference is {@code null}.
     */
    public static void checkNotNull(Object reference) {
        checkNotNull(reference, "A null value is not allowed here.");
    }
}
