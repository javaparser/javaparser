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

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import java.util.List;
import java.util.Optional;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

/**
 * @author Federico Tomassetti
 */
public class StatementContext<N extends Statement> extends AbstractJavaParserContext<N> {

    public StatementContext(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public static SymbolReference<? extends ResolvedValueDeclaration> solveInBlock(String name, TypeSolver typeSolver, Statement stmt) {
        if (!(requireParentNode(stmt) instanceof NodeWithStatements)) {
            throw new IllegalArgumentException();
        }
        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) requireParentNode(stmt);
        int position = -1;
        for (int i = 0; i < blockStmt.getStatements().size(); i++) {
            if (blockStmt.getStatements().get(i).equals(stmt)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(blockStmt.getStatements().get(i), typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return JavaParserFactory.getContext(requireParentNode(stmt), typeSolver).solveSymbol(name);
    }

    public static Optional<Value> solveInBlockAsValue(String name, TypeSolver typeSolver, Statement stmt) {
        if (!(requireParentNode(stmt) instanceof NodeWithStatements)) {
            throw new IllegalArgumentException();
        }
        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) requireParentNode(stmt);
        int position = -1;
        for (int i = 0; i < blockStmt.getStatements().size(); i++) {
            if (blockStmt.getStatements().get(i).equals(stmt)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(blockStmt.getStatements().get(i), typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return Optional.of(Value.from(symbolReference.getCorrespondingDeclaration()));
            }
        }

        // if nothing is found we should ask the parent context
        return JavaParserFactory.getContext(requireParentNode(stmt), typeSolver).solveSymbolAsValue(name);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {

        // if we're in a multiple Variable declaration line (for ex: double a=0, b=a;)
        SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(wrappedNode, typeSolver);
        Optional<Value> symbolReference = solveWithAsValue(symbolDeclarator, name);
        if (symbolReference.isPresent()) {
            return symbolReference;
        }

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (requireParentNode(wrappedNode) instanceof com.github.javaparser.ast.body.MethodDeclaration) {
            return getParent().solveSymbolAsValue(name);
        }
        if (requireParentNode(wrappedNode) instanceof LambdaExpr) {
            return getParent().solveSymbolAsValue(name);
        }
        if (requireParentNode(wrappedNode) instanceof IfStmt) {
            return getParent().solveSymbolAsValue(name);
        }
        if (!(requireParentNode(wrappedNode) instanceof NodeWithStatements)) {
            return getParent().solveSymbolAsValue(name);
        }
        NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) requireParentNode(wrappedNode);
        int position = -1;
        for (int i = 0; i < nodeWithStmt.getStatements().size(); i++) {
            if (nodeWithStmt.getStatements().get(i).equals(wrappedNode)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            symbolDeclarator = JavaParserFactory.getSymbolDeclarator(nodeWithStmt.getStatements().get(i), typeSolver);
            symbolReference = solveWithAsValue(symbolDeclarator, name);
            if (symbolReference.isPresent()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        Context parentContext = getParent();
        return parentContext.solveSymbolAsValue(name);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {

        // if we're in a multiple Variable declaration line (for ex: double a=0, b=a;)
        SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(wrappedNode, typeSolver);
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
        if (symbolReference.isSolved()) {
            return symbolReference;
        }

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (requireParentNode(wrappedNode) instanceof com.github.javaparser.ast.body.MethodDeclaration) {
            return getParent().solveSymbol(name);
        }
        if (requireParentNode(wrappedNode) instanceof com.github.javaparser.ast.body.ConstructorDeclaration) {
            return getParent().solveSymbol(name);
        }
        if (requireParentNode(wrappedNode) instanceof LambdaExpr) {
            return getParent().solveSymbol(name);
        }
        if (!(requireParentNode(wrappedNode) instanceof NodeWithStatements)) {
            return getParent().solveSymbol(name);
        }
        NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) requireParentNode(wrappedNode);
        int position = -1;
        for (int i = 0; i < nodeWithStmt.getStatements().size(); i++) {
            if (nodeWithStmt.getStatements().get(i).equals(wrappedNode)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            symbolDeclarator = JavaParserFactory.getSymbolDeclarator(nodeWithStmt.getStatements().get(i), typeSolver);
            symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return getParent().solveMethod(name, argumentsTypes, false);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        return getParent().solveType(name);
    }
}
