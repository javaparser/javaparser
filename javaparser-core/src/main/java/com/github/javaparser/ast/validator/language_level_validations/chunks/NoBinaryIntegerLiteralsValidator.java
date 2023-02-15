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
package com.github.javaparser.ast.validator.language_level_validations.chunks;

import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.LiteralStringValueExpr;
import com.github.javaparser.ast.expr.LongLiteralExpr;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.VisitorValidator;

public class NoBinaryIntegerLiteralsValidator extends VisitorValidator {

    @Override
    public void visit(IntegerLiteralExpr n, ProblemReporter arg) {
        validate(n, arg);
        super.visit(n, arg);
    }

    @Override
    public void visit(LongLiteralExpr n, ProblemReporter arg) {
        validate(n, arg);
        super.visit(n, arg);
    }

    private static void validate(LiteralStringValueExpr n, ProblemReporter arg) {
        if (n.getValue().toUpperCase().startsWith("0B")) {
            arg.report(n, "Binary literal values are not supported.");
        }
    }
}
