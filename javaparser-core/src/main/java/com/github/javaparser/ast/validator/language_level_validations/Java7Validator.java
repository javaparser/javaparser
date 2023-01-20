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

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.UnionType;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;

/**
 * This validator validates according to Java 7 syntax rules.
 */
public class Java7Validator extends Java6Validator {

    final SingleNodeTypeValidator<TryStmt> tryWithLimitedResources = new SingleNodeTypeValidator<>(TryStmt.class, (n, reporter) -> {
        if (n.getCatchClauses().isEmpty() && n.getResources().isEmpty() && !n.getFinallyBlock().isPresent()) {
            reporter.report(n, "Try has no finally, no catch, and no resources.");
        }
        for (Expression resource : n.getResources()) {
            if (!resource.isVariableDeclarationExpr()) {
                reporter.report(n, "Try with resources only supports variable declarations.");
            }
        }
    });

    private final SingleNodeTypeValidator<UnionType> multiCatch = new SingleNodeTypeValidator<>(UnionType.class, (n, reporter) -> {
        // Case "0 elements" is caught elsewhere.
        if (n.getElements().size() == 1) {
            reporter.report(n, "Union type (multi catch) must have at least two elements.");
        }
    });

    public Java7Validator() {
        super();
        remove(genericsWithoutDiamondOperator);
        replace(tryWithoutResources, tryWithLimitedResources);
        remove(noBinaryIntegerLiterals);
        remove(noUnderscoresInIntegerLiterals);
        replace(noMultiCatch, multiCatch);
    }
}
