/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

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
                        JavaParserSymbolDeclaration decl = JavaParserSymbolDeclaration.localVar(v, typeSolver);
                        return Optional.of(Value.from(decl));
                    }
                }
            }
        }

        if (requireParentNode(wrappedNode) instanceof BlockStmt) {
            return StatementContext.solveInBlockAsValue(name, typeSolver, wrappedNode);
        } else {
            return getParent().solveSymbolAsValue(name);
        }
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

        if (requireParentNode(wrappedNode) instanceof BlockStmt) {
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
