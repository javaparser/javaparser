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
package com.github.javaparser.ast.validator.language_level_validations;

/**
 * This validator validates according to Java 15 syntax rules -- including incubator/preview/second preview features.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/15/">https://openjdk.java.net/projects/jdk/15/</a>
 */
public class Java15PreviewValidator extends Java15Validator {

    public Java15PreviewValidator() {
        super();
        // Incubator
        // No new incubator language features added within Java 15
        // Preview
        // remove(noSealedClasses); // Sealed Classes - first preview within Java 15 - https://openjdk.java.net/jeps/360
        // 2nd Preview
        // Pattern Matching for instanceof - 2nd preview in Java 15 - https://openjdk.java.net/jeps/305
        remove(noPatternMatchingInstanceOf);
        {
            // Records - 2nd preview within Java 15 - https://openjdk.java.net/jeps/384
            remove(noRecordDeclaration);
            add(recordAsTypeIdentifierNotAllowed);
            add(recordDeclarationValidator);
        }
    }
}
