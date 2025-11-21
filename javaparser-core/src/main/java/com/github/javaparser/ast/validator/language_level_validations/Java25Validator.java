/*
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

import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.Validator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.FlexibleConstructorValidator;

/**
 * This validator validates according to Java 25 syntax rules.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/25/">https://openjdk.java.net/projects/jdk/25/</a>
 */
public class Java25Validator extends Java22Validator {

    final Validator flexibleConstructorValidator =
            new SingleNodeTypeValidator<>(ConstructorDeclaration.class, new FlexibleConstructorValidator());

    public Java25Validator() {
        super();
        add(flexibleConstructorValidator);
    }
}
