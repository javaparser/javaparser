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
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.PatternExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithStatements;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFactory;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
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
        if (!(demandParentNode(stmt) instanceof NodeWithStatements)) {
            throw new IllegalArgumentException();
        }
        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) demandParentNode(stmt);
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
        return JavaParserFactory.getContext(demandParentNode(stmt), typeSolver).solveSymbol(name);
    }

    public static Optional<Value> solveInBlockAsValue(String name, TypeSolver typeSolver, Statement stmt) {
        if (!(demandParentNode(stmt) instanceof NodeWithStatements)) {
            throw new IllegalArgumentException();
        }
        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) demandParentNode(stmt);
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
        return JavaParserFactory.getContext(demandParentNode(stmt), typeSolver).solveSymbolAsValue(name);
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
        if(!getParent().isPresent()) {
            return Optional.empty();
        }
        Context parentContext = getParent().get();
        Node parentOfWrappedNode = demandParentNode(wrappedNode);

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (parentOfWrappedNode instanceof MethodDeclaration) {
            return parentContext.solveSymbolAsValue(name);
        }else if (parentOfWrappedNode instanceof LambdaExpr) {
            return parentContext.solveSymbolAsValue(name);
        } else if (parentOfWrappedNode instanceof IfStmt) {
            // FIXME: Ignore this -- logic should be contained within the IfStatementContext re: whether it exposes any types / variables.
//            // Only try to get the patternExprs from the IfStmt condition if we're directly inside the "then" section
//            // ... or if we're in the condition
//            if (nodeContextIsThenOfIfStmt(getParent().get())) {
//                List<PatternExpr> patternExprs = getParent().get().patternExprsExposedToChild(wrappedNode);
//                for (PatternExpr patternExpr : patternExprs) {
//                    if (patternExpr.getName().getIdentifier().equals(name)) {
//                        JavaParserSymbolDeclaration decl = JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver);
//                        return Optional.of(Value.from(decl));
//                    }
//                }
//            } else if (nodeContextIsConditionOfIfStmt(getParent().get())) {
//                List<PatternExpr> patternExprs = getParent().get().patternExprsExposedToChild(wrappedNode);
//                for (PatternExpr patternExpr : patternExprs) {
//                    if (patternExpr.getName().getIdentifier().equals(name)) {
//                        JavaParserSymbolDeclaration decl = JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver);
//                        return Optional.of(Value.from(decl));
//                    }
//                }
//            }

            // Otherwise continue up the scope chain as normal...
            return parentContext.solveSymbolAsValue(name);
        } else if (!(parentOfWrappedNode instanceof NodeWithStatements)) {
            return parentContext.solveSymbolAsValue(name);
        }

        NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) parentOfWrappedNode;
        int position = -1;

        // Get the position of the wrapped node.
        for (int i = 0; i < nodeWithStmt.getStatements().size(); i++) {
            if (nodeWithStmt.getStatements().get(i).equals(wrappedNode)) {
                position = i;
            }
        }
        if (position == -1) {
            throw new RuntimeException();
        }

        // Working backwards from the node, try to solve the symbol. This limits the scope to declarations that appear prior to usage.
        for (int statementIndex = position - 1; statementIndex >= 0; statementIndex--) {
            Statement statement = nodeWithStmt.getStatements().get(statementIndex);
            symbolDeclarator = JavaParserFactory.getSymbolDeclarator(statement, typeSolver);
            symbolReference = solveWithAsValue(symbolDeclarator, name);
            if (symbolReference.isPresent()) {
                return symbolReference;
            }
        }

        // If nothing is found we should ask the parent context.
        return solveSymbolAsValueInParentContext(name);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {

        // if we're in a multiple Variable declaration line (for ex: double a=0, b=a;)
        // FIXME: This makes pattern expression variables available when resolving the right hand side of a BinaryExpr...
        SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(wrappedNode, typeSolver);
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
        if (symbolReference.isSolved()) {
            return symbolReference;
        }

        // If no parent context / node, no point continuing... TODO: Tidy this up.
        Context parentContext = getParent().orElseThrow(() -> new RuntimeException("Parent context unexpectedly empty."));
        Node parentOfWrappedNode = demandParentNode(wrappedNode);


        // FIXME: Ignore this -- logic should be contained within the IfStatementContext re: whether it exposes any types / variables.
//        // If this is the "then" section of an if/else if (i.e. not an else) -- e.g. wrappedNode of ExpressionStmt
//        // ... consider pattern expressions defined within the IfStmt condition
//        boolean nodeContextIsThenOfIfStmt = nodeContextIsThenOfIfStmt(parentContext);
//        if (nodeContextIsThenOfIfStmt) {
//            List<PatternExpr> patternExprs = parentContext.patternExprsExposedToChild(getWrappedNode());
//            for (PatternExpr patternExpr : patternExprs) {
//                if (patternExpr.getName().getIdentifier().equals(name)) {
//                    return SymbolReference.solved(JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver));
//                }
//            }
//        }

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (parentOfWrappedNode instanceof MethodDeclaration) {
            return parentContext.solveSymbol(name);
        }
        if (parentOfWrappedNode instanceof ConstructorDeclaration) {
            return parentContext.solveSymbol(name);
        }
        if (parentOfWrappedNode instanceof LambdaExpr) {
            return parentContext.solveSymbol(name);
        }
        if (!(parentOfWrappedNode instanceof NodeWithStatements)) {
            return parentContext.solveSymbol(name);
        }
        NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) parentOfWrappedNode;
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
        return solveSymbolInParentContext(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false);
    }

}
