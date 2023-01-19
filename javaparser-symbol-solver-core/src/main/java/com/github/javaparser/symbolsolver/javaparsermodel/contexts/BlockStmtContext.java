/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

public class BlockStmtContext extends AbstractJavaParserContext<BlockStmt> {

    public BlockStmtContext(BlockStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        int position = wrappedNode.getStatements().indexOf(child);
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
            ExpressionStmt expressionStmt = (ExpressionStmt) statement;
            if (expressionStmt.getExpression() instanceof VariableDeclarationExpr) {
                VariableDeclarationExpr variableDeclarationExpr = (VariableDeclarationExpr) expressionStmt.getExpression();
                List<VariableDeclarator> variableDeclarators = new LinkedList<>();
                variableDeclarators.addAll(variableDeclarationExpr.getVariables());
                return variableDeclarators;
            }
        }
        return Collections.emptyList();
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        Optional<Context> optionalParent = getParent();
        if (!optionalParent.isPresent()) {
            return SymbolReference.unsolved();
        }

        if (wrappedNode.getStatements().size() > 0) {
            // tries to resolve a declaration from local variables defined in child statements
            // or from parent node context
            // for example resolve declaration for the MethodCallExpr a.method() in
            // A a = this;
            // {
            //   a.method();
            // }

            List<VariableDeclarator> variableDeclarators = new LinkedList<>();
            // find all variable declarators exposed to child
            // given that we don't know the statement we are trying to resolve, we look for all variable declarations 
            // defined in the context of the wrapped node whether it is located before or after the statement that interests us 
            // because a variable cannot be (re)defined after having been used
            wrappedNode.getStatements().getLast().ifPresent(stmt -> variableDeclarators.addAll(localVariablesExposedToChild(stmt)));
            if (!variableDeclarators.isEmpty()) {
                // FIXME: Work backwards from the current statement, to only consider declarations prior to this statement.
                for (VariableDeclarator vd : variableDeclarators) {
                    if (vd.getNameAsString().equals(name)) {
                        return SymbolReference.solved(JavaParserSymbolDeclaration.localVar(vd, typeSolver));
                    }
                }
            }
        }

        // Otherwise continue as normal...
        return solveSymbolInParentContext(name);
    }
}
