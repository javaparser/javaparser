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

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

import java.util.List;
import java.util.Optional;

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.model.declarations.MethodDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.TypeDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.resolution.Value;
import com.github.javaparser.symbolsolver.model.typesystem.Type;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

/**
 * @author Federico Tomassetti
 */
public class StatementContext<N extends Statement> extends AbstractJavaParserContext<N> {

    public StatementContext(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public static SymbolReference<? extends ValueDeclaration> solveInBlock(String name, TypeSolver typeSolver, Statement stmt) {
        if (!(getParentNode(stmt) instanceof NodeWithStatements)) { // was BlockStmt
            throw new IllegalArgumentException();
        }
        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) getParentNode(stmt);
        int position = -1;
        for (int i = 0; i < blockStmt.getStmts().size(); i++) {
            if (blockStmt.getStmts().get(i).equals(stmt)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(blockStmt.getStmts().get(i), typeSolver);
            SymbolReference<? extends ValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return JavaParserFactory.getContext(getParentNode(stmt), typeSolver).solveSymbol(name, typeSolver);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name, TypeSolver typeSolver) {

        // if we're in a multiple Variable declaration line (for ex: double a=0, b=a;)
        SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(wrappedNode, typeSolver);
        Optional<Value> symbolReference = solveWithAsValue(symbolDeclarator, name, typeSolver);
        if (symbolReference.isPresent()) {
            return symbolReference;
        }

      // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (getParentNode(wrappedNode) instanceof com.github.javaparser.ast.body.MethodDeclaration) {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
        if (getParentNode(wrappedNode) instanceof LambdaExpr) {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
        if (getParentNode(wrappedNode) instanceof IfStmt) {
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
        if (!(getParentNode(wrappedNode) instanceof NodeWithStatements)) { // was BlockStmt
            return getParent().solveSymbolAsValue(name, typeSolver);
        }
        NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) getParentNode(wrappedNode);
        int position = -1;
        for (int i = 0; i < nodeWithStmt.getStmts().size(); i++) {
            if (nodeWithStmt.getStmts().get(i).equals(wrappedNode)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
            symbolDeclarator = JavaParserFactory.getSymbolDeclarator(nodeWithStmt.getStmts().get(i), typeSolver);
            symbolReference = solveWithAsValue(symbolDeclarator, name, typeSolver);
            if (symbolReference.isPresent()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        Context parentContext = getParent();
        return parentContext.solveSymbolAsValue(name, typeSolver);
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {

        // if we're in a multiple Variable declaration line (for ex: double a=0, b=a;)
        SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(wrappedNode, typeSolver);
        SymbolReference<? extends ValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
        if (symbolReference.isSolved()) {
            return symbolReference;
        }

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (getParentNode(wrappedNode) instanceof com.github.javaparser.ast.body.MethodDeclaration) {
            return getParent().solveSymbol(name, typeSolver);
        }
        if (getParentNode(wrappedNode) instanceof com.github.javaparser.ast.body.ConstructorDeclaration) {
            return getParent().solveSymbol(name, typeSolver);
        }
        if (getParentNode(wrappedNode) instanceof LambdaExpr) {
            return getParent().solveSymbol(name, typeSolver);
        }
        if (!(getParentNode(wrappedNode) instanceof NodeWithStatements)) { // was BlockStmt
            return getParent().solveSymbol(name, typeSolver);
        }
        NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) getParentNode(wrappedNode);
        int position = -1;
        for (int i = 0; i < nodeWithStmt.getStmts().size(); i++) {
            if (nodeWithStmt.getStmts().get(i).equals(wrappedNode)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }
        for (int i = position - 1; i >= 0; i--) {
             symbolDeclarator = JavaParserFactory.getSymbolDeclarator(nodeWithStmt.getStmts().get(i), typeSolver);
            symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
        }

        // if nothing is found we should ask the parent context
        return getParent().solveSymbol(name, typeSolver);
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> argumentsTypes, TypeSolver typeSolver) {
        return getParent().solveMethod(name, argumentsTypes, typeSolver);
    }

    @Override
    public SymbolReference<TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        return getParent().solveType(name, typeSolver);
    }
}
