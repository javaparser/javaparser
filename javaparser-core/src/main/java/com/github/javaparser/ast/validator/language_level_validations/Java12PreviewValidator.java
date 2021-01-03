/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package com.github.javaparser.ast.validator.language_level_validations;

/**
 * This validator validates according to Java 12 syntax rules -- including incubator, preview, and second preview features.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/12/">https://openjdk.java.net/projects/jdk/12/</a>
 */
public class Java12PreviewValidator extends Java12Validator {

    public Java12PreviewValidator() {
        super();

        // Incubator
        // No new incubator language features added in Java 12

        // Preview
        remove(noSwitchExpressions); // Switch Expressions - first preview in Java 12 - https://openjdk.java.net/jeps/325
        remove(onlyOneLabelInSwitchCase); // Switch Expressions - first preview in Java 12 - https://openjdk.java.net/jeps/325

        // 2nd Preview
        // No new 2nd preview language features added in Java 12


    }
}
