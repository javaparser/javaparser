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
 * GNU Lesser General Public Package for more details.
 */
package com.github.javaparser.ast.validator.language_level_validations;

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.CompactClassValidator;

/**
 * Validator for Java 25 language features.
 * Java 25 introduces JEP 512: Compact Source Files and Instance Main Methods.
 * This validator extends Java 24 to support the new compact source file syntax.
 *
 * Uses CompactClassValidator for comprehensive validation of:
 * - Compact class restrictions (cannot extend/implement, implicitly final)
 * - Flexible main method signatures (static/instance, void/int, with/without String[] args)
 */
public class Java25Validator extends Java24Validator {

    public Java25Validator() {
        super();
        add(new SingleNodeTypeValidator<>(ClassOrInterfaceDeclaration.class, new CompactClassValidator()));
    }
}
