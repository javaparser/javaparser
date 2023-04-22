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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.VarType;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.TypedValidator;
import java.util.Optional;

public class VarValidator implements TypedValidator<VarType> {

    private boolean varAllowedInLambdaParameters;

    public VarValidator(boolean varAllowedInLambdaParameters) {
        this.varAllowedInLambdaParameters = varAllowedInLambdaParameters;
    }

    @Override
    public void accept(VarType node, ProblemReporter reporter) {
        // All allowed locations are within a VariableDeclaration inside a VariableDeclarationExpr inside something else.
        Optional<VariableDeclarator> variableDeclarator = node.findAncestor(VariableDeclarator.class);
        if (!variableDeclarator.isPresent()) {
            // Java 11's var in lambda's
            if (varAllowedInLambdaParameters) {
                boolean valid = node.findAncestor(Parameter.class).flatMap(Node::getParentNode).map((Node p) -> p instanceof LambdaExpr).orElse(false);
                if (valid) {
                    return;
                }
            }
            reportIllegalPosition(node, reporter);
            return;
        }
        variableDeclarator.ifPresent(vd -> {
            if (vd.getType().isArrayType()) {
                reporter.report(vd, "\"var\" cannot have extra array brackets.");
            }
            Optional<Node> variableDeclarationExpr = vd.getParentNode();
            if (!variableDeclarationExpr.isPresent()) {
                reportIllegalPosition(node, reporter);
                return;
            }
            variableDeclarationExpr.ifPresent(vdeNode -> {
                if (!(vdeNode instanceof VariableDeclarationExpr)) {
                    reportIllegalPosition(node, reporter);
                    return;
                }
                VariableDeclarationExpr vde = (VariableDeclarationExpr) vdeNode;
                if (vde.getVariables().size() > 1) {
                    reporter.report(vde, "\"var\" only takes a single variable.");
                }
                Optional<Node> container = vdeNode.getParentNode();
                if (!container.isPresent()) {
                    reportIllegalPosition(node, reporter);
                    return;
                }
                container.ifPresent(c -> {
                    boolean positionIsFine = c instanceof ForStmt || c instanceof ForEachStmt || c instanceof ExpressionStmt || c instanceof TryStmt;
                    if (!positionIsFine) {
                        reportIllegalPosition(node, reporter);
                    }
                    // A local variable declaration ends up inside an ExpressionStmt.
                    if (c instanceof ExpressionStmt) {
                        if (!vd.getInitializer().isPresent()) {
                            reporter.report(node, "\"var\" needs an initializer.");
                        }
                        vd.getInitializer().ifPresent(initializer -> {
                            if (initializer instanceof NullLiteralExpr) {
                                reporter.report(node, "\"var\" cannot infer type from just null.");
                            }
                            if (initializer instanceof ArrayInitializerExpr) {
                                reporter.report(node, "\"var\" cannot infer array types.");
                            }
                        });
                    }
                });
            });
        });
    }

    private void reportIllegalPosition(VarType n, ProblemReporter reporter) {
        reporter.report(n, "\"var\" is not allowed here.");
    }
}
