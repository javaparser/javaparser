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

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.RecordDeclaration;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;

import java.util.List;

/**
 * This validator validates according to Java 16 syntax rules.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/16/">https://openjdk.java.net/projects/jdk/16/</a>
 */
public class Java16Validator extends Java15Validator {

    final SingleNodeTypeValidator<RecordDeclaration> forbidNonStaticFieldsInRecords = new SingleNodeTypeValidator<>(RecordDeclaration.class, (n, reporter) -> {
        long count = n.getFields().stream()
                .filter(fieldDeclaration -> !fieldDeclaration.isStatic())
                .count();

        if (count > 0) {
            reporter.report(n, "Record Declarations must have zero non-static fields.");
        }
    });

    final SingleNodeTypeValidator<RecordDeclaration> validateRecordComponentAccessors = new SingleNodeTypeValidator<>(RecordDeclaration.class, (n, reporter) -> {

        n.getParameters().forEach(parameter -> {
            List<MethodDeclaration> methodsByName = n.getMethodsByName(parameter.getNameAsString());

            methodsByName.stream()
                    .filter(methodDeclaration -> methodDeclaration.getParameters().isEmpty())
                    .forEach(methodDeclaration -> {
                        if (!methodDeclaration.getType().equals(parameter.getType())) {
                            reporter.report(
                                    n,
                                    String.format(
                                            "Incorrect component accessor return type. Expected: '%s', found: '%s'.",
                                            parameter.getTypeAsString(),
                                            methodDeclaration.getTypeAsString()
                                    )
                            );
                        }
                    });
        });

    });

    public Java16Validator() {
        super();

        // Released Language Features
        remove(noPatternMatchingInstanceOf); // Pattern Matching for instanceof released within Java 16 - https://openjdk.java.net/jeps/305
        remove(noRecordDeclaration); // Records released within Java 16 - https://openjdk.java.net/jeps/395

        add(forbidNonStaticFieldsInRecords);
        add(validateRecordComponentAccessors);
    }
}
