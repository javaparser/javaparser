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
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
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

import static com.github.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class StatementContext<N extends Statement> extends AbstractJavaParserContext<N> {

    public StatementContext(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public static SymbolReference<? extends ResolvedValueDeclaration> solveInBlock(String name, TypeSolver typeSolver, Statement stmt) {
        Node parentNode = demandParentNode(stmt);
        if (!(parentNode instanceof NodeWithStatements)) {
            throw new IllegalArgumentException();
        }
        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) parentNode;
        boolean flag=true;
        for(Statement statement:blockStmt.getStatements()){
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(statement, typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return symbolReference;
            }
            if(statement.equals(stmt)){
                flag=false;
                break;
            }
        }
        if(flag){
            throw new RuntimeException();
        }

        // if nothing is found we should ask the parent context
        return JavaParserFactory.getContext(parentNode, typeSolver).solveSymbol(name);
    }

    public static Optional<Value> solveInBlockAsValue(String name, TypeSolver typeSolver, Statement stmt) {
        Node parentNode = demandParentNode(stmt);
        if (!(parentNode instanceof NodeWithStatements)) {
            throw new IllegalArgumentException();
        }
        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) parentNode;
        boolean flag=true;
        for(Statement statement:blockStmt.getStatements()){
            SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(statement, typeSolver);
            SymbolReference<? extends ResolvedValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
            if (symbolReference.isSolved()) {
                return Optional.of(Value.from(symbolReference.getCorrespondingDeclaration()));
            }
            if(statement.equals(stmt)){
                flag=false;
                break;
            }
        }
        if(flag){
            throw new RuntimeException();
        }

        // if nothing is found we should ask the parent context
        return JavaParserFactory.getContext(parentNode, typeSolver).solveSymbolAsValue(name);
    }

    @Override
    public Optional<Value> solveSymbolAsValue(String name) {

        // if we're in a multiple Variable declaration line (for ex: double a=0, b=a;)
        SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(wrappedNode, typeSolver);
        Optional<Value> symbolReference = solveWithAsValue(symbolDeclarator, name);
        if (symbolReference.isPresent()) {
            return symbolReference;
        }

        // If there is no parent
        if (!getParent().isPresent()) {
            return Optional.empty();
        }
        Context parentContext = getParent().get();
        Node parentOfWrappedNode = demandParentNode(wrappedNode);

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (parentOfWrappedNode instanceof NodeWithStatements) {
            NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) parentOfWrappedNode;
            boolean flag = true;
            for (Statement statement : nodeWithStmt.getStatements()) {
                if (statement.equals(wrappedNode)) {
                    flag = false;
                    break;
                }
                symbolDeclarator = JavaParserFactory.getSymbolDeclarator(statement, typeSolver);
                symbolReference = solveWithAsValue(symbolDeclarator, name);
                if (symbolReference.isPresent()) {
                    return symbolReference;
                }
            }
            if (flag) {
                throw new RuntimeException();
            }
        }

        // if nothing is found we should ask the parent context
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

        // If no parent context / node, no point continuing... TODO: Tidy this up.
        Context parentContext = getParent().orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."));
        Node parentOfWrappedNode = demandParentNode(wrappedNode);

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (parentOfWrappedNode instanceof NodeWithStatements) {
            NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) parentOfWrappedNode;
            boolean flag = true;
            for (Statement statement : nodeWithStmt.getStatements()) {
                if (statement.equals(wrappedNode)) {
                    flag = false;
                    break;
                }
                symbolDeclarator = JavaParserFactory.getSymbolDeclarator(statement, typeSolver);
                symbolReference = solveWith(symbolDeclarator, name);
                if (symbolReference.isSolved()) {
                    return symbolReference;
                }
            }
            if (flag) {
                throw new RuntimeException();
            }
        }

//        if (parentOfWrappedNode instanceof MethodDeclaration) {
//            return parentContext.solveSymbol(name);
//        }
//        if (parentOfWrappedNode instanceof ConstructorDeclaration) {
//            return parentContext.solveSymbol(name);
//        }
//        if (parentOfWrappedNode instanceof LambdaExpr) {
//            return parentContext.solveSymbol(name);
//        }
        // if nothing is found we should ask the parent context
        return parentContext.solveSymbol(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        return getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveMethod(name, argumentsTypes, false);
    }

    @Override
    public SymbolReference<ResolvedTypeDeclaration> solveType(String name) {
        return getParent()
                .orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."))
                .solveType(name);
    }
}
