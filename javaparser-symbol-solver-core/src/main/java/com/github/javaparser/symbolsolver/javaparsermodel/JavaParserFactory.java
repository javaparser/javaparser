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

package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.SymbolDeclarator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.*;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.*;

import static com.github.javaparser.resolution.Navigator.demandParentNode;

/**
 * @author Federico Tomassetti
 */
public class JavaParserFactory {

    public static Context getContext(Node node, TypeSolver typeSolver) {
        if (node == null) {
            throw new NullPointerException("Node should not be null");
        }


        if (node instanceof ArrayAccessExpr) {
            return new ArrayAccessExprContext((ArrayAccessExpr) node, typeSolver);
        }
            if (node instanceof AnnotationDeclaration) {
            return new AnnotationDeclarationContext((AnnotationDeclaration) node, typeSolver);
        }
            if (node instanceof BinaryExpr) {
            return new BinaryExprContext((BinaryExpr) node, typeSolver);
        }
            if (node instanceof BlockStmt) {
            return new BlockStmtContext((BlockStmt) node, typeSolver);
        }
            if (node instanceof CompilationUnit) {
            return new CompilationUnitContext((CompilationUnit) node, typeSolver);
        }
            if (node instanceof EnclosedExpr) {
            return new EnclosedExprContext((EnclosedExpr) node, typeSolver);
        }
            if (node instanceof ForEachStmt) {
            return new ForEachStatementContext((ForEachStmt) node, typeSolver);
        }
            if (node instanceof ForStmt) {
            return new ForStatementContext((ForStmt) node, typeSolver);
        }
            if (node instanceof IfStmt) {
            return new IfStatementContext((IfStmt) node, typeSolver);
        }
            if (node instanceof InstanceOfExpr) {
            return new InstanceOfExprContext((InstanceOfExpr) node, typeSolver);
        }
            if (node instanceof LambdaExpr) {
            return new LambdaExprContext((LambdaExpr) node, typeSolver);
        }
            if (node instanceof MethodDeclaration) {
            return new MethodContext((MethodDeclaration) node, typeSolver);
        }
            if (node instanceof ConstructorDeclaration) {
            return new ConstructorContext((ConstructorDeclaration) node, typeSolver);
        }
            if (node instanceof ClassOrInterfaceDeclaration) {
            return new ClassOrInterfaceDeclarationContext((ClassOrInterfaceDeclaration) node, typeSolver);
        }
            if (node instanceof MethodCallExpr) {
            return new MethodCallExprContext((MethodCallExpr) node, typeSolver);
        }
            if (node instanceof MethodReferenceExpr) {
            return new MethodReferenceExprContext((MethodReferenceExpr) node, typeSolver);
        }
            if (node instanceof EnumDeclaration) {
            return new EnumDeclarationContext((EnumDeclaration) node, typeSolver);
        }
            if (node instanceof FieldAccessExpr) {
            return new FieldAccessContext((FieldAccessExpr) node, typeSolver);
        }
            if (node instanceof SwitchEntry) {
            return new SwitchEntryContext((SwitchEntry) node, typeSolver);
        }
            if (node instanceof TryStmt) {
            return new TryWithResourceContext((TryStmt) node, typeSolver);
        }
            if (node instanceof Statement) {
            return new StatementContext<>((Statement) node, typeSolver);
        }
            if (node instanceof CatchClause) {
            return new CatchClauseContext((CatchClause) node, typeSolver);
        }
            if (node instanceof UnaryExpr) {
            return new UnaryExprContext((UnaryExpr) node, typeSolver);
        }
            if (node instanceof VariableDeclarator) {
            return new VariableDeclaratorContext((VariableDeclarator) node, typeSolver);
        }
            if (node instanceof VariableDeclarationExpr) {
            return new VariableDeclarationExprContext((VariableDeclarationExpr) node, typeSolver);
        }
            if (node instanceof ObjectCreationExpr &&
            ((ObjectCreationExpr) node).getAnonymousClassBody().isPresent()) {
            return new AnonymousClassDeclarationContext((ObjectCreationExpr) node, typeSolver);
        }
            if (node instanceof ObjectCreationExpr) {
            return new ObjectCreationContext((ObjectCreationExpr)node, typeSolver);
        }
        if (node instanceof NameExpr) {
                // to resolve a name when in a fieldAccess context, we can go up until we get a node other than FieldAccessExpr,
                // in order to prevent a infinite loop if the name is the same as the field (ie x.x, x.y.x, or x.y.z.x)
                if (node.getParentNode().isPresent() && node.getParentNode().get() instanceof FieldAccessExpr) {
                    Node ancestor = node.getParentNode().get();
                    while (ancestor.getParentNode().isPresent()) {
                        ancestor = ancestor.getParentNode().get();
                        if (!(ancestor instanceof FieldAccessExpr)) {
                            break;
                        }
                    }
                    return getContext(ancestor, typeSolver);
                }
                if (node.getParentNode().isPresent() && node.getParentNode().get() instanceof ObjectCreationExpr && node.getParentNode().get().getParentNode().isPresent()) {
                    return getContext(node.getParentNode().get().getParentNode().get(), typeSolver);
                }
            }
        final Node parentNode = demandParentNode(node);
        if (node instanceof ClassOrInterfaceType && parentNode instanceof ClassOrInterfaceDeclaration) {
                ClassOrInterfaceDeclaration parentDeclaration = (ClassOrInterfaceDeclaration) parentNode;
                if (parentDeclaration.getImplementedTypes().contains(node) ||
                    parentDeclaration.getExtendedTypes().contains(node)) {
                    // When resolving names in implements and extends the body of the declaration
                    // should not be searched so use limited context.
                    return new ClassOrInterfaceDeclarationExtendsContext(parentDeclaration, typeSolver);
                }
            }
        return getContext(parentNode, typeSolver);
    }

    public static SymbolDeclarator getSymbolDeclarator(Node node, TypeSolver typeSolver) {
        if (node instanceof FieldDeclaration) {
            return new FieldSymbolDeclarator((FieldDeclaration) node, typeSolver);
        }
        if (node instanceof Parameter) {
            return new ParameterSymbolDeclarator((Parameter) node, typeSolver);
        }
        if (node instanceof PatternExpr) {
            return new PatternSymbolDeclarator((PatternExpr) node, typeSolver);
        }
        if (node instanceof ExpressionStmt) {
            ExpressionStmt expressionStmt = (ExpressionStmt) node;
            if (expressionStmt.getExpression() instanceof VariableDeclarationExpr) {
                return new VariableSymbolDeclarator((VariableDeclarationExpr) (expressionStmt.getExpression()),
                        typeSolver);
            }
            return new NoSymbolDeclarator<>(expressionStmt, typeSolver);
        }
        if (node instanceof ForEachStmt) {
            ForEachStmt foreachStmt = (ForEachStmt) node;
            return new VariableSymbolDeclarator(foreachStmt.getVariable(), typeSolver);
        }
        return new NoSymbolDeclarator<>(node, typeSolver);
    }

}
