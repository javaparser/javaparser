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

import java.util.Collections;
import java.util.List;
import java.util.ListIterator;
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class StatementContext<N extends Statement> extends AbstractJavaParserContext<N> {

    public StatementContext(N wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    public static SymbolReference<? extends ResolvedValueDeclaration> solveInBlock(String name, TypeSolver typeSolver, Statement stmt) {
        Optional<Node> optionalParentNode = stmt.getParentNode();
        if(!optionalParentNode.isPresent()) {
             return SymbolReference.unsolved(ResolvedValueDeclaration.class);
        }

        Node parentOfWrappedNode = optionalParentNode.get();
        if (!(parentOfWrappedNode instanceof NodeWithStatements)) {
            throw new IllegalArgumentException();
        }

        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) parentOfWrappedNode;
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
        return JavaParserFactory.getContext(parentOfWrappedNode, typeSolver).solveSymbol(name);
    }

    public static Optional<Value> solveInBlockAsValue(String name, TypeSolver typeSolver, Statement stmt) {
        Optional<Node> optionalParentNode = stmt.getParentNode();
        if(!optionalParentNode.isPresent()) {
            return Optional.empty();
        }

        Node parentOfWrappedNode = optionalParentNode.get();
        if (!(parentOfWrappedNode instanceof NodeWithStatements)) {
            throw new IllegalArgumentException();
        }

        NodeWithStatements<?> blockStmt = (NodeWithStatements<?>) parentOfWrappedNode;
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
        return JavaParserFactory.getContext(parentOfWrappedNode, typeSolver).solveSymbolAsValue(name);
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

        Optional<Node> optionalParentNode = wrappedNode.getParentNode();
        if(!optionalParentNode.isPresent()) {
            return Optional.empty();
        }

        Node parentOfWrappedNode = optionalParentNode.get();

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (parentOfWrappedNode instanceof MethodDeclaration) {
            return parentContext.solveSymbolAsValue(name);
        }else if (parentOfWrappedNode instanceof LambdaExpr) {
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
    protected Optional<Value> solveWithAsValue(SymbolDeclarator symbolDeclarator, String name) {
//        symbolDeclarator.getSymbolDeclarations().get(0).
//        ResolvedValueDeclaration resolvedValueDeclaration = symbolDeclarator.getSymbolDeclarations().get(0);
//        boolean isVariable = resolvedValueDeclaration.isVariable();
        // TODO: Try to get the context of the declarator / initialisations -- then check if the declarations themselves match (or vice versa)
        return super.solveWithAsValue(symbolDeclarator, name);
    }

    @Override
    public SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name) {
        return solveSymbol(name, true);
    }

    /**
     * Used where a symbol is being used (e.g. solving {@code x} when used as an argument {@code doubleThis(x)}, or calculation {@code return x * 2;}).
     * @param name the variable / reference / identifier used.
     * @param iterateAdjacentStmts flag to iterate adjacent statements, should be set to {@code true} except when calling itself in order to prevent revisiting already visited symbols.
     * @return // FIXME: Better documentation on how this is different to solveSymbolAsValue()
     */
    private SymbolReference<? extends ResolvedValueDeclaration> solveSymbol(String name, boolean iterateAdjacentStmts) {

        /*
         * If we're in a variable declaration line.
         * Example: {@code double a=0, b=a;}
         * Example: {@code a instanceof String s;}
         */
        SymbolDeclarator symbolDeclarator = JavaParserFactory.getSymbolDeclarator(wrappedNode, typeSolver);
        SymbolReference<? extends ResolvedValueDeclaration> symbolReference = solveWith(symbolDeclarator, name);
        if (symbolReference.isSolved()) {
            return symbolReference;
        }

        /*
         * If we're in a statement that contains a pattern expression.
         * Example: {@code double x = a instanceof String s;}
         */
        List<PatternExpr> patternExprs = patternExprsExposedFromChildren();
        for (int i = 0; i < patternExprs.size(); i++) {
            PatternExpr patternExpr = patternExprs.get(i);
            if(patternExpr.getNameAsString().equals(name)) {
                return SymbolReference.solved(JavaParserSymbolDeclaration.patternVar(patternExpr, typeSolver));
            }
        }

        Optional<Node> optionalParentNode = wrappedNode.getParentNode();
        if(!optionalParentNode.isPresent()) {
            return SymbolReference.unsolved(ResolvedValueDeclaration.class);
        }

        Node parentOfWrappedNode = optionalParentNode.get();

        // we should look in all the statements preceding, treating them as SymbolDeclarators
        if (parentOfWrappedNode instanceof MethodDeclaration) {
            return solveSymbolInParentContext(name);
        } else if (parentOfWrappedNode instanceof ConstructorDeclaration) {
            return solveSymbolInParentContext(name);
        } else if (parentOfWrappedNode instanceof LambdaExpr) {
            return solveSymbolInParentContext(name);
        } else if (parentOfWrappedNode instanceof NodeWithStatements) {
            // If we choose to not solve adjacent statements abort the solution process here.
            // In the calling context (the context that calls this) we will attempt to
            // resolve all prior adjacent statements, and then the common parent as the fallback.
            // Then the common parent will check all of its prior adjacent statements, etc.

            // Further below is a more detailed explanation for why we may want to disable this visitation of adjacent statements
            // to prevent revisiting the same contexts over and over again.
            if (!iterateAdjacentStmts) {
                return SymbolReference.unsolved(ResolvedValueDeclaration.class);
            }

            NodeWithStatements<?> nodeWithStmt = (NodeWithStatements<?>) parentOfWrappedNode;

            // Assuming the wrapped node exists within the parent's collection of statements...
            int position = nodeWithStmt.getStatements().indexOf(wrappedNode);
            if (position == -1) {
                throw new IllegalStateException("This node is not a statement within the current NodeWithStatements");
            }

            // Start at the current node and work backwards...
            ListIterator<Statement> statementListIterator = nodeWithStmt.getStatements().listIterator(position);
            while(statementListIterator.hasPrevious()) {
                Context prevContext = JavaParserFactory.getContext(statementListIterator.previous(), typeSolver);
                if (prevContext instanceof StatementContext) {
                    // We have an explicit check for "StatementContext" to prevent a factorial increase of visited statements.
                    //
                    // For example consider the following:
                    //   String a = "a";
                    //   String b = "b";
                    //   String c = get();
                    //
                    // If we simply call "prevContext.solveSymbol(name)" we will call the current method with the adjacent statement "prevContext".
                    // Then "prevContext" will look at its previous adjacent statement. And so on and so forth.
                    // When there are no more previous statements in this chain of method calls, we come back to here...
                    // Then we look at the next "prevContext" which causes the entire process to start again.
                    // This is how we get a factorial increase in calls to "solveSymbol".
                    //
                    // So what we do instead with this check is we pass in a flag to say "Do not look at previous adjacent statements".
                    // Since each visited "prevContext" does not look at its adjacent statements we only visit each statement once in this while loop.
                    symbolReference = ((StatementContext<?>)prevContext).solveSymbol(name, false);
                } else {
                    symbolReference = prevContext.solveSymbol(name);
                }
                if (symbolReference.isSolved()) {
                    return symbolReference;
                }
            }
        }

        // If nothing is found, attempt to solve within the parent context
        return solveSymbolInParentContext(name);
    }

    @Override
    public SymbolReference<ResolvedMethodDeclaration> solveMethod(String name, List<ResolvedType> argumentsTypes, boolean staticOnly) {
        // TODO: Document why staticOnly is forced to be false.
        return solveMethodInParentContext(name, argumentsTypes, false);
    }


    @Override
    public List<PatternExpr> patternExprsExposedFromChildren() {
        // Statements never make pattern expressions available.
        return Collections.emptyList();

    }

    @Override
    public List<PatternExpr> negatedPatternExprsExposedFromChildren() {
        // Statements never make pattern expressions available.
        return Collections.emptyList();
    }

}
