/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2025 The JavaParser Team.
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

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.Validator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.CompactClassValidator;

/**
 * Validator for Java 25 language features.
 *
 * Implements JEP 512: Compact Source Files and Instance Main Methods.
 *
 * Additional features for Java 25:
 * - JEP 511 (Module Imports) - not yet implemented
 * - JEP 513 (Flexible Constructor Bodies) - not yet implemented
 *
 * @see <a href="https://openjdk.org/jeps/512">JEP 512</a>
 */
public class Java25Validator extends Java22Validator {

    /**
     * Validator for compact classes introduced in JEP 512.
     * Validates:
     * - Compact classes cannot extend other classes
     * - Compact classes cannot implement interfaces
     * - Compact classes are implicitly final
     * - Main methods have valid signatures (instance or static, void or int return)
     */
    final Validator compactClassValidator =
            new SingleNodeTypeValidator<>(ClassOrInterfaceDeclaration.class, new CompactClassValidator());

    public Java25Validator() {
        super();
        // JEP 512: Compact Source Files and Instance Main Methods
        add(compactClassValidator);
    }
}
