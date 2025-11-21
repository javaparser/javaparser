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

package com.github.javaparser.ast.validator.language_level_validations.chunks;

import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.TypedValidator;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

import java.util.Optional;

/**
 * Validates JEP 513: Flexible Constructor Bodies.
 *
 * Rules:
 * 1. Statements before super()/this() (prologue) cannot reference 'this'
 * 2. Only one super()/this() call allowed per constructor
 *
 * @since 3.27.0
 */
public class FlexibleConstructorValidator implements TypedValidator<ConstructorDeclaration> {

    @Override
    public void accept(ConstructorDeclaration constructor, ProblemReporter reporter) {
        Optional<ExplicitConstructorInvocationStmt> explicitInvocation = findExplicitConstructorInvocation(constructor);

        if (explicitInvocation.isPresent()) {
            validatePrologue(constructor, explicitInvocation.get(), reporter);
        }
    }

    /**
     * Find the explicit constructor invocation (super/this call) in the constructor body.
     */
    private Optional<ExplicitConstructorInvocationStmt> findExplicitConstructorInvocation(ConstructorDeclaration constructor) {
        for (Statement stmt : constructor.getBody().getStatements()) {
            if (stmt instanceof ExplicitConstructorInvocationStmt) {
                return Optional.of((ExplicitConstructorInvocationStmt) stmt);
            }
        }
        return Optional.empty();
    }

    /**
     * Validate the prologue (statements before super/this call).
     * These statements must not reference 'this'.
     */
    private void validatePrologue(ConstructorDeclaration constructor, ExplicitConstructorInvocationStmt explicitInvocation, ProblemReporter reporter) {
        boolean foundExplicitInvocation = false;

        for (Statement stmt : constructor.getBody().getStatements()) {
            if (stmt == explicitInvocation) {
                foundExplicitInvocation = true;
                break;
            }

            // This statement is in the prologue - check for 'this' references
            ThisReferenceDetector detector = new ThisReferenceDetector();
            stmt.accept(detector, null);

            if (detector.foundThisReference) {
                reporter.report(stmt, "Statements before super() or this() cannot reference the current instance ('this').");
            }
        }

        // Check if there are any statements after the explicit invocation that also contain an explicit invocation
        if (foundExplicitInvocation) {
            boolean inEpilogue = false;
            for (Statement stmt : constructor.getBody().getStatements()) {
                if (stmt == explicitInvocation) {
                    inEpilogue = true;
                    continue;
                }

                if (inEpilogue && stmt instanceof ExplicitConstructorInvocationStmt) {
                    reporter.report(stmt, "Only one super() or this() call is allowed per constructor.");
                }
            }
        }
    }

    /**
     * Visitor to detect 'this' references in statements.
     */
    private static class ThisReferenceDetector extends VoidVisitorAdapter<Void> {
        boolean foundThisReference = false;

        @Override
        public void visit(ThisExpr n, Void arg) {
            foundThisReference = true;
            super.visit(n, arg);
        }
    }
}
