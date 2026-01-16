/*
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.SingleNodeTypeValidator;
import com.github.javaparser.ast.validator.Validator;
import com.github.javaparser.resolution.Navigator;

/**
 * This validator validates according to Java 22 syntax rules.
 *
 * @see <a href="https://openjdk.java.net/projects/jdk/22/">https://openjdk.java.net/projects/jdk/22/</a>
 */
public class Java22Validator extends Java21Validator {

    final Validator unnamedVarOnlyWhereAllowedByJep456 =
            new SingleNodeTypeValidator<>(SimpleName.class, (name, reporter) -> {
                if (!name.getIdentifier().equals("_")) {
                    return;
                }
                if (reportNoParent(name, reporter)) {
                    return;
                }
                Node parentNode = name.getParentNode().get();
                if (parentNode instanceof VariableDeclarator || parentNode instanceof TypePatternExpr) {
                    return;
                }
                if (parentNode instanceof Parameter) {
                    Parameter parameter = (Parameter) parentNode;
                    if (reportNoParent(parameter, reporter)) {
                        return;
                    }
                    Node grandParent = parameter.getParentNode().get();
                    if (grandParent instanceof CatchClause || grandParent instanceof LambdaExpr) {
                        return;
                    }
                }
                try {
                    ForStmt enclosingFor =
                            (ForStmt) Navigator.demandParentNode(name, ancestor -> ancestor instanceof ForStmt);
                    if (enclosingFor.getCompare().isPresent()
                            && enclosingFor.getCompare().get().containsWithinRange(name)) {
                        // In a for compare, so now check that it's the LHS of an assignment
                        AssignExpr enclosingAssign = (AssignExpr)
                                Navigator.demandParentNode(name, ancestor -> ancestor instanceof AssignExpr);
                        if (enclosingAssign.getTarget().containsWithinRange(name)) {
                            return;
                        }
                    }
                } catch (IllegalStateException e) {
                    // Didn't find a ForStmt ancestor, so the "_" identifier should not be allowed here.
                }
                reporter.report(name, "Unnamed variables only supported in cases described by JEP456");
            });

    final Validator matchAllPatternNotTopLevel =
            new SingleNodeTypeValidator<>(MatchAllPatternExpr.class, (patternExpr, reporter) -> {
                if (!patternExpr.getParentNode().isPresent()
                        || !(patternExpr.getParentNode().get() instanceof PatternExpr)) {
                    reporter.report(patternExpr, "MatchAllPatternExpr cannot be used as a top-level pattern");
                }
            });

    private boolean reportNoParent(Node node, ProblemReporter reporter) {
        if (node.getParentNode().isPresent()) {
            return false;
        }
        String className = node.getClass().getCanonicalName();
        reporter.report(node, "Node of type " + className + " must have an AST parent");
        return true;
    }

    public Java22Validator() {
        super();
        remove(underscoreKeywordValidator);
        add(unnamedVarOnlyWhereAllowedByJep456);
        add(matchAllPatternNotTopLevel);
    }
}
