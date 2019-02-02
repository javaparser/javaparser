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

package com.github.javaparser.symbolsolver.javaparsermodel;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.*;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.*;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.FieldSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.NoSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.ParameterSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.VariableSymbolDeclarator;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.requireParentNode;

/**
 * @author Federico Tomassetti
 */
public class JavaParserFactory {

    public static Context getContext(Node node, TypeSolver typeSolver) {
        if (node == null) {
            throw new NullPointerException("Node should not be null");
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
                // to resolve a name when in a fieldAccess context, we can get to the grand parent to prevent a infinite loop if the name is the same as the field (ie x.x)
                if (node.getParentNode().isPresent() && node.getParentNode().get() instanceof FieldAccessExpr && node.getParentNode().get().getParentNode().isPresent()) {
                    return getContext(node.getParentNode().get().getParentNode().get(), typeSolver);
                }
                if (node.getParentNode().isPresent() && node.getParentNode().get() instanceof ObjectCreationExpr && node.getParentNode().get().getParentNode().isPresent()) {
                    return getContext(node.getParentNode().get().getParentNode().get(), typeSolver);
                }
            }
            final Node parentNode = requireParentNode(node);
            if (parentNode instanceof ObjectCreationExpr
                    && (node == ((ObjectCreationExpr) parentNode).getType()
                        || ((ObjectCreationExpr) parentNode).getArguments().contains(node))) {
                return getContext(requireParentNode(parentNode), typeSolver);
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
        } else {
            throw new IllegalArgumentException(node.getClass().getCanonicalName());
        }
    }
}
