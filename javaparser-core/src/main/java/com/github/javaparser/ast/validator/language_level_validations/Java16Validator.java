/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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
 * This validator validates according to Java 16 syntax rules.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/16/">https://openjdk.java.net/projects/jdk/16/</a>
 */
public class Java16Validator extends Java15Validator {

    public Java16Validator() {
        super();
        // Released Language Features
        // Pattern Matching for instanceof released within Java 16 - https://openjdk.java.net/jeps/305
        remove(noPatternMatchingInstanceOf);
        {
            // Records released within Java 16 - https://openjdk.java.net/jeps/395
            remove(noRecordDeclaration);
            // local interface released within Java 16 -
            // https://docs.oracle.com/javase/specs/jls/se16/html/jls-14.html#jls-14.3
            remove(innerClasses);
            add(recordAsTypeIdentifierNotAllowed);
            add(recordDeclarationValidator);
        }
    }
}
