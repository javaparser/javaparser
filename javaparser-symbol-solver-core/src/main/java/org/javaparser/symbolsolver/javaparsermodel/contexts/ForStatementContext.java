/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2020 The JavaParser Team.
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

package org.javaparser.symbolsolver.javaparsermodel.contexts;

import org.javaparser.ast.Node;
import org.javaparser.ast.body.VariableDeclarator;
import org.javaparser.ast.expr.AssignExpr;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.ast.expr.VariableDeclarationExpr;
import org.javaparser.ast.nodeTypes.NodeWithStatements;
import org.javaparser.ast.stmt.ForStmt;
import org.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import org.javaparser.resolution.declarations.ResolvedValueDeclaration;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import org.javaparser.symbolsolver.model.resolution.SymbolReference;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.LinkedList;
import java.util.List;

import static org.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

public class ForStatementContext extends AbstractJavaParserContext<ForStmt> {

    public ForStatementContext(ForStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Expression expression : wrappedNode.getInitialization()) {
            if (expression instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) expression;
                for (VariableDeclarator variableDeclarator : variableDeclarationExpr.getVariables()) {
                    if (variableDeclarator.getName().getId().equals(name)) {
                        return SymbolReference.solved(JavaParserSymbolDeclaration.localVar(variableDeclarator, typeSolver));
                    }
                }
            } else if (!(expression instanceof AssignExpr || expression instanceof MethodCallExpr)) {
                throw new UnsupportedOperationException(expression.getClass().getCanonicalName());
            }
        }

        if (demandParentNode(wrappedNode) instanceof NodeWithStatements) {
            return StatementContext.solveInBlock(name, typeSolver, wrappedNode);
        } else {
            return getParent().solveSymbol(name);
        }
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes,
                                                                  boolean staticOnly) {
        return getParent().solveMethod(name, argumentsTypes, false);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        List<VariableDeclarator> res = new LinkedList<>();
        for (Expression expression : wrappedNode.getInitialization()) {
            if (expression instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) expression;
                res.addAll(variableDeclarationExpr.getVariables());
            }
        }
        return res;
    }
}
