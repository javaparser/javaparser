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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.Value;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.github.javaparser.resolution.Navigator.demandParentNode;

public class TryWithResourceContext extends AbstractJavaParserContext<TryStmt> {

    public TryWithResourceContext(TryStmt wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {
        for (Expression expr : wrappedNode.getResources()) {
            if (expr instanceof VariableDeclarationExpr) {
                for (VariableDeclarator v : ((VariableDeclarationExpr)expr).getVariables()) {
                    if (v.getName().getIdentifier().equals(name)) {
                        ResolvedValueDeclaration decl = JavaParserSymbolDeclaration.localVar(v, typeSolver);
                        return Optional.of(Value.from(decl));
                    }
                }
            }
        }

        if (demandParentNode(wrappedNode) instanceof BlockStmt) {
            return StatementContext.solveInBlockAsValue(name, typeSolver, wrappedNode);
        }
        return solveSymbolAsValueInParentContext(name);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        for (Expression expr : wrappedNode.getResources()) {
            if (expr instanceof VariableDeclarationExpr) {
                for (VariableDeclarator v : ((VariableDeclarationExpr)expr).getVariables()) {
                    if (v.getName().getIdentifier().equals(name)) {
                        return SymbolReference.solved(JavaParserSymbolDeclaration.localVar(v, typeSolver));
                    }
                }
            }
        }

        if (demandParentNode(wrappedNode) instanceof BlockStmt) {
            return StatementContext.solveInBlock(name, typeSolver, wrappedNode);
        }
        return solveSymbolInParentContext(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false);
    }

    @Override
    public List<VariableDeclarator> localVariablesExposedToChild(Node child) {
        NodeList<Expression> resources = wrappedNode.getResources();
        for (int i=0;i<resources.size();i++) {
            if (child == resources.get(i)) {
                return resources.subList(0, i).stream()
                        .map(e -> e instanceof VariableDeclarationExpr ? ((VariableDeclarationExpr) e).getVariables()
                                : Collections.<VariableDeclarator>emptyList())
                        .flatMap(List::stream)
                        .collect(Collectors.toList());
            }
        }
        if (child == wrappedNode.getTryBlock()) {
            List<VariableDeclarator> res = new LinkedList<>();
            for (Expression expr : resources) {
                if (expr instanceof VariableDeclarationExpr) {
                    res.addAll(((VariableDeclarationExpr)expr).getVariables());
                }
            }
            return res;
        }
        return Collections.emptyList();
    }
}
