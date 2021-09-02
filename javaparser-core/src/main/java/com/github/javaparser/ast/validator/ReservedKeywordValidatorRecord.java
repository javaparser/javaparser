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
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Validates that "record" cannot be used as class name.
 * For details, see <a href="https://openjdk.java.net/jeps/395">JEP 395</a>
 */
public class ReservedKeywordValidatorRecord extends VisitorValidator {
    private final String keyword;
    private final String error;

    public ReservedKeywordValidatorRecord() {
        this.keyword = "record";
        error = f("'%s' cannot be used as an identifier as it is a keyword.", keyword);
    }

    @Override
    public void visit(Name n, ProblemReporter arg) {
        if (n.getIdentifier().equals(keyword) && usedAsClassOrInterfaceName(n)) {
            arg.report(n, error);
        }
        super.visit(n, arg);
    }

    @Override
    public void visit(SimpleName n, ProblemReporter arg) {
        if (n.getIdentifier().equals(keyword) && usedAsClassOrInterfaceName(n)) {
            arg.report(n, error);
        }
        super.visit(n, arg);
    }

    private boolean usedAsClassOrInterfaceName(Node n) {
        if (!n.getParentNode().isPresent()) {
            return false;
        }
        Node parent = n.getParentNode().get();
        return (parent instanceof ClassOrInterfaceDeclaration);
    }
}
