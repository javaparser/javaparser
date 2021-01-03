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

import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.Validator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.ModifierValidator;
import com.github.javaparser.ast.validator.language_level_validations.chunks.UnderscoreKeywordValidator;

/**
 * This validator validates according to Java 9 syntax rules.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk9/">https://openjdk.java.net/projects/jdk9/</a>
 */
public class Java9Validator extends Java8Validator {
    final Validator underscoreKeywordValidator = new UnderscoreKeywordValidator();
    final Validator modifiers = new ModifierValidator(true, true, true);
    final SingleNodeTypeValidator<TryStmt> tryWithResources = new SingleNodeTypeValidator<>(TryStmt.class, (n, reporter) -> {
        if (n.getCatchClauses().isEmpty()
                && n.getResources().isEmpty()
                && !n.getFinallyBlock().isPresent()) {
            reporter.report(n, "Try has no finally, no catch, and no resources.");
        }
    });

    public Java9Validator() {
        super();
        add(underscoreKeywordValidator);
        remove(noModules);
        replace(modifiersWithoutPrivateInterfaceMethods, modifiers);
        replace(tryWithLimitedResources, tryWithResources);
    }
}
