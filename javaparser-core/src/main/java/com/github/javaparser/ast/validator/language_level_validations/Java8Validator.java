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

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.Validator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.ModifierValidator;

/**
 * This validator validates according to Java 8 syntax rules.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk8/">https://openjdk.java.net/projects/jdk8/</a>
 * @see <a href="https://openjdk.java.net/projects/jdk8/features">https://openjdk.java.net/projects/jdk8/features</a>
 */
public class Java8Validator extends Java7Validator {

    final Validator modifiersWithoutPrivateInterfaceMethods = new ModifierValidator(true, true, false);

    final Validator defaultMethodsInInterface = new SingleNodeTypeValidator<>(ClassOrInterfaceDeclaration.class, (n, reporter) -> {
        if (n.isInterface()) {
            n.getMethods().forEach(m -> {
                if (m.isDefault() && !m.getBody().isPresent()) {
                    reporter.report(m, "'default' methods must have a body.");
                }
            });
        }
    });

    public Java8Validator() {
        super();
        replace(modifiersWithoutDefaultAndStaticInterfaceMethodsAndPrivateInterfaceMethods, modifiersWithoutPrivateInterfaceMethods);
        add(defaultMethodsInInterface);
        remove(noLambdas);
        // TODO validate more annotation locations http://openjdk.java.net/jeps/104
        // TODO validate repeating annotations http://openjdk.java.net/jeps/120
    }
}
