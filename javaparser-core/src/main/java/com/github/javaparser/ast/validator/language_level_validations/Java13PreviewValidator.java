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
 * This validator validates according to Java 13 syntax rules -- including incubator/preview/second preview features.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/13/">https://openjdk.java.net/projects/jdk/13/</a>
 */
public class Java13PreviewValidator extends Java13Validator {

    public Java13PreviewValidator() {
        super();

        // Incubator
        // No new incubator language features added in Java 13

        // Preview
        remove(noTextBlockLiteral); // Text Block Literals - first preview in Java 13 - https://openjdk.java.net/jeps/355

        // 2nd Preview
        remove(onlyOneLabelInSwitchCase); // Switch Expressions - 2nd preview in Java 13 - https://openjdk.java.net/jeps/354
        remove(noSwitchExpressions); // Switch Expressions - 2nd preview in Java 13 - https://openjdk.java.net/jeps/354
        remove(noYield); // Switch Expressions - 2nd preview in Java 13 - https://openjdk.java.net/jeps/354

    }
}
