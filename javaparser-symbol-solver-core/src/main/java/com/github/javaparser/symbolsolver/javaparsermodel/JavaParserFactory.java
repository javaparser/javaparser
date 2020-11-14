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

package com.github.javaparser.symbolsolver.javaparsermodel;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.demandParentNode;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EnumConstantDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.AnnotationDeclarationContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.AnonymousClassDeclarationContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.BlockStmtContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.CatchClauseContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ClassOrInterfaceDeclarationContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.CompilationUnitContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ConstructorContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.EnumDeclarationContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.FieldAccessContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ForEachStatementContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ForStatementContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.LambdaExprContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodCallExprContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodReferenceExprContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.ObjectCreationContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.StatementContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.SwitchEntryContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.TryWithResourceContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.VariableDeclarationExprContext;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.VariableDeclaratorContext;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserAnnotationDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserEnumDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserInterfaceDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.FieldSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.NoSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.ParameterSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.VariableSymbolDeclarator;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

/**
 * @author Federico Tomassetti
 */
public class JavaParserFactory {

    public static Context getContext(Node node, TypeSolver typeSolver) {
        if (node == null) {
            throw new NullPointerException("Node should not be null");
        } else if (node instanceof AnnotationDeclaration) {
            return new AnnotationDeclarationContext((AnnotationDeclaration) node, typeSolver);
        } else if (node instanceof BlockStmt) {
            return new BlockStmtContext((BlockStmt) node, typeSolver);
        } else if (node instanceof CompilationUnit) {
            return new CompilationUnitContext((CompilationUnit) node, typeSolver);
        } else if (node instanceof ForEachStmt) {
            return new ForEachStatementContext((ForEachStmt) node, typeSolver);
        } else if (node instanceof ForStmt) {
            return new ForStatementContext((ForStmt) node, typeSolver);
        } else if (node instanceof LambdaExpr) {
            return new LambdaExprContext((LambdaExpr) node, typeSolver);
        } else if (node instanceof MethodDeclaration) {
            return new MethodContext((MethodDeclaration) node, typeSolver);
        } else if (node instanceof ConstructorDeclaration) {
            return new ConstructorContext((ConstructorDeclaration) node, typeSolver);
        } else if (node instanceof ClassOrInterfaceDeclaration) {
            return new ClassOrInterfaceDeclarationContext((ClassOrInterfaceDeclaration) node, typeSolver);
        } else if (node instanceof MethodCallExpr) {
            return new MethodCallExprContext((MethodCallExpr) node, typeSolver);
        } else if (node instanceof MethodReferenceExpr) {
            return new MethodReferenceExprContext((MethodReferenceExpr) node, typeSolver);
        } else if (node instanceof EnumDeclaration) {
            return new EnumDeclarationContext((EnumDeclaration) node, typeSolver);
        } else if (node instanceof FieldAccessExpr) {
            return new FieldAccessContext((FieldAccessExpr) node, typeSolver);
        } else if (node instanceof SwitchEntry) {
            return new SwitchEntryContext((SwitchEntry) node, typeSolver);
        } else if (node instanceof TryStmt) {
            return new TryWithResourceContext((TryStmt) node, typeSolver);
        } else if (node instanceof Statement) {
            return new StatementContext<>((Statement) node, typeSolver);
        } else if (node instanceof CatchClause) {
            return new CatchClauseContext((CatchClause) node, typeSolver);
        } else if (node instanceof VariableDeclarator) {
            return new VariableDeclaratorContext((VariableDeclarator) node, typeSolver);
        } else if (node instanceof VariableDeclarationExpr) {
            return new VariableDeclarationExprContext((VariableDeclarationExpr) node, typeSolver);
        } else if (node instanceof ObjectCreationExpr &&
            ((ObjectCreationExpr) node).getAnonymousClassBody().isPresent()) {
            return new AnonymousClassDeclarationContext((ObjectCreationExpr) node, typeSolver);
        } else if (node instanceof ObjectCreationExpr) {
            return new ObjectCreationContext((ObjectCreationExpr)node, typeSolver);
        } else {
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
            if (parentNode instanceof ObjectCreationExpr
                    && (node == ((ObjectCreationExpr) parentNode).getType()
                        || ((ObjectCreationExpr) parentNode).getArguments().contains(node))) {
                return getContext(demandParentNode(parentNode), typeSolver);
            }
            if (parentNode == null) {
                throw new IllegalStateException("The AST node does not appear to be inserted in a propert AST, therefore we cannot resolve symbols correctly");
            }
            return getContext(parentNode, typeSolver);
        }
    }

    public static SymbolDeclarator getSymbolDeclarator(Node node, TypeSolver typeSolver) {
        if (node instanceof FieldDeclaration) {
            return new FieldSymbolDeclarator((FieldDeclaration) node, typeSolver);
        } else if (node instanceof Parameter) {
            return new ParameterSymbolDeclarator((Parameter) node, typeSolver);
        } else if (node instanceof ExpressionStmt) {
            ExpressionStmt expressionStmt = (ExpressionStmt) node;
            if (expressionStmt.getExpression() instanceof VariableDeclarationExpr) {
                return new VariableSymbolDeclarator((VariableDeclarationExpr) (expressionStmt.getExpression()), typeSolver);
            } else {
                return new NoSymbolDeclarator<>(expressionStmt, typeSolver);
            }
        } else if (node instanceof IfStmt) {
            return new NoSymbolDeclarator<>((IfStmt) node, typeSolver);
        } else if (node instanceof ForEachStmt) {
            ForEachStmt foreachStmt = (ForEachStmt) node;
            return new VariableSymbolDeclarator(foreachStmt.getVariable(), typeSolver);
        } else {
            return new NoSymbolDeclarator<>(node, typeSolver);
        }
    }

    public static ResolvedReferenceTypeDeclaration toTypeDeclaration(Node node, TypeSolver typeSolver) {
        if (node instanceof ClassOrInterfaceDeclaration) {
            if (((ClassOrInterfaceDeclaration) node).isInterface()) {
                return new JavaParserInterfaceDeclaration((ClassOrInterfaceDeclaration) node, typeSolver);
            } else {
                return new JavaParserClassDeclaration((ClassOrInterfaceDeclaration) node, typeSolver);
            }
        } else if (node instanceof TypeParameter) {
            return new JavaParserTypeParameter((TypeParameter) node, typeSolver);
        } else if (node instanceof EnumDeclaration) {
            return new JavaParserEnumDeclaration((EnumDeclaration) node, typeSolver);
        } else if (node instanceof AnnotationDeclaration) {
            return new JavaParserAnnotationDeclaration((AnnotationDeclaration) node, typeSolver);
        } else if (node instanceof EnumConstantDeclaration) {
            return new JavaParserEnumDeclaration((EnumDeclaration) demandParentNode((EnumConstantDeclaration) node), typeSolver);
        } else {
            throw new IllegalArgumentException(node.getClass().getCanonicalName());
        }
    }
}
