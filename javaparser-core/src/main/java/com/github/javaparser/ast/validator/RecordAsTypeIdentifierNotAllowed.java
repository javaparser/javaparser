/*
 * Copyright (C) 2021 The JavaParser Team.
 * Copyright (C) 2021 Oliver Kopp
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
package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;

/**
 * Validates that "record" cannot be used as identifier for type declarations (e.g., classes, enums, and records).
 * For details, see <a href="https://openjdk.java.net/jeps/395">JEP 395</a>
 */
public class RecordAsTypeIdentifierNotAllowed extends VisitorValidator {

    private final String error;

    public RecordAsTypeIdentifierNotAllowed() {
        error = "'record' is a restricted identifier and cannot be used for type declarations";
    }

    @Override
    public void visit(Name n, ProblemReporter arg) {
        if (n.getIdentifier().equals("record") && !validUsage(n)) {
            arg.report(n, error);
        }
        super.visit(n, arg);
    }

    @Override
    public void visit(SimpleName n, ProblemReporter arg) {
        if (n.getIdentifier().equals("record") && !validUsage(n)) {
            arg.report(n, error);
        }
        super.visit(n, arg);
    }

    private boolean validUsage(Node node) {
        if (!node.getParentNode().isPresent()) {
            return true;
        }
        Node parent = node.getParentNode().get();
        return !(parent instanceof TypeDeclaration);
    }
}
