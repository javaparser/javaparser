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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

public class BlockStmtContext extends AbstractJavaParserContext<BlockStmt> {

    public BlockStmtContext(BlockStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        int position = -1;
        for (int i = 0; i < wrappedNode.getStatements().size(); i++) {
            if (wrappedNode.getStatements().get(i).equals(child)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        List<VariableDeclarator> variableDeclarators = new LinkedList<>();
        for (int i = position - 1; i >= 0; i--) {
            variableDeclarators.addAll(localVariablesDeclaredIn(wrappedNode.getStatement(i)));
        }
        return variableDeclarators;
    }

    private List<VariableDeclarator> localVariablesDeclaredIn(Statement statement) {
        if (statement instanceof ExpressionStmt) {
            ExpressionStmt expressionStmt = (ExpressionStmt)statement;
            if (expressionStmt.getExpression() instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr)expressionStmt.getExpression();
                List<VariableDeclarator> variableDeclarators = new LinkedList<>();
                variableDeclarators.addAll(variableDeclarationExpr.getVariables());
                return variableDeclarators;
            }
        }
        return Collections.emptyList();
    }
}
