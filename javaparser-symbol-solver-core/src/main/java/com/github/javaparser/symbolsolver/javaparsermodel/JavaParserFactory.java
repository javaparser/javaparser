/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

import static com.github.javaparser.resolution.Navigator.demandParentNode;

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
import java.util.Optional;

/**
 * @author Federico Tomassetti
 */
public class JavaParserFactory {

    public static Context getContext(Node node, TypeSolver typeSolver) {
        if (node == null) {
            throw new NullPointerException("Node should not be null");
        }

        if (node instanceof ArrayAccessExpr expr) {
            return new ArrayAccessExprContext(expr, typeSolver);
        }
        if (node instanceof AnnotationDeclaration declaration) {
            return new AnnotationDeclarationContext(declaration, typeSolver);
        }
        if (node instanceof BinaryExpr expr1) {
            return new BinaryExprContext(expr1, typeSolver);
        }
        if (node instanceof BlockStmt stmt) {
            return new BlockStmtContext(stmt, typeSolver);
        }
        if (node instanceof CompilationUnit unit) {
            return new CompilationUnitContext(unit, typeSolver);
        }
        if (node instanceof EnclosedExpr expr2) {
            return new EnclosedExprContext(expr2, typeSolver);
        }
        if (node instanceof ForEachStmt stmt1) {
            return new ForEachStatementContext(stmt1, typeSolver);
        }
        if (node instanceof ForStmt stmt2) {
            return new ForStatementContext(stmt2, typeSolver);
        }
        if (node instanceof IfStmt stmt3) {
            return new IfStatementContext(stmt3, typeSolver);
        }
        if (node instanceof WhileStmt stmt4) {
            return new WhileStatementContext(stmt4, typeSolver);
        }
        if (node instanceof DoStmt stmt5) {
            return new DoStatementContext(stmt5, typeSolver);
        }
        if (node instanceof InstanceOfExpr expr3) {
            return new InstanceOfExprContext(expr3, typeSolver);
        }
        if (node instanceof LambdaExpr expr4) {
            return new LambdaExprContext(expr4, typeSolver);
        }
        if (node instanceof MethodDeclaration declaration1) {
            return new MethodContext(declaration1, typeSolver);
        }
        if (node instanceof ConstructorDeclaration declaration2) {
            return new ConstructorContext(declaration2, typeSolver);
        }
        if (node instanceof ClassOrInterfaceDeclaration declaration3) {
            return new ClassOrInterfaceDeclarationContext(declaration3, typeSolver);
        }
        if (node instanceof MethodCallExpr expr5) {
            return new MethodCallExprContext(expr5, typeSolver);
        }
        if (node instanceof MethodReferenceExpr expr6) {
            return new MethodReferenceExprContext(expr6, typeSolver);
        }
        if (node instanceof EnumDeclaration declaration4) {
            return new EnumDeclarationContext(declaration4, typeSolver);
        }
        if (node instanceof RecordDeclaration declaration5) {
            return new RecordDeclarationContext(declaration5, typeSolver);
        }
        if (node instanceof FieldAccessExpr expr7) {
            return new FieldAccessContext(expr7, typeSolver);
        }
        if (node instanceof SwitchEntry entry) {
            return new SwitchEntryContext(entry, typeSolver);
        }
        if (node instanceof TryStmt stmt6) {
            return new TryWithResourceContext(stmt6, typeSolver);
        }
        if (node instanceof Statement statement) {
            return new StatementContext<>(statement, typeSolver);
        }
        if (node instanceof CatchClause clause) {
            return new CatchClauseContext(clause, typeSolver);
        }
        if (node instanceof UnaryExpr expr8) {
            return new UnaryExprContext(expr8, typeSolver);
        }
        if (node instanceof VariableDeclarator declarator) {
            return new VariableDeclaratorContext(declarator, typeSolver);
        }
        if (node instanceof VariableDeclarationExpr expr9) {
            return new VariableDeclarationExprContext(expr9, typeSolver);
        }
        if (node instanceof ObjectCreationExpr expr10
                && expr10.getAnonymousClassBody().isPresent()) {
            return new AnonymousClassDeclarationContext(expr10, typeSolver);
        }
        if (node instanceof ObjectCreationExpr expr11) {
            return new ObjectCreationContext(expr11, typeSolver);
        }
        if (node instanceof ConditionalExpr expr12) {
            return new ConditionalExprContext(expr12, typeSolver);
        }
        if (node instanceof NameExpr) {
            // to resolve a name when in a fieldAccess context, we can go up until we get a node other than
            // FieldAccessExpr,
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
            if (node.getParentNode().isPresent()
                    && node.getParentNode().get() instanceof ObjectCreationExpr
                    && node.getParentNode().get().getParentNode().isPresent()) {
                return getContext(node.getParentNode().get().getParentNode().get(), typeSolver);
            }
        }
        final Node parentNode = demandParentNode(node);
        if (node instanceof ClassOrInterfaceType && parentNode instanceof ClassOrInterfaceDeclaration parentDeclaration) {
            if (parentDeclaration.getImplementedTypes().contains(node)
                    || parentDeclaration.getExtendedTypes().contains(node)) {
                // When resolving names in implements and extends the body of the declaration
                // should not be searched so use limited context.
                return new ClassOrInterfaceDeclarationExtendsContext(parentDeclaration, typeSolver);
            }
        }
        return getContext(parentNode, typeSolver);
    }

    public static SymbolDeclarator getSymbolDeclarator(Node node, TypeSolver typeSolver) {
        if (node instanceof FieldDeclaration declaration) {
            return new FieldSymbolDeclarator(declaration, typeSolver);
        }
        if (node instanceof Parameter parameter) {
            return new ParameterSymbolDeclarator(parameter, typeSolver);
        }
        if (node instanceof TypePatternExpr expr) {
            return new TypePatternSymbolDeclarator(expr, typeSolver);
        }
        if (node instanceof ExpressionStmt expressionStmt) {
            if (expressionStmt.getExpression().isVariableDeclarationExpr()) {
                return new VariableSymbolDeclarator(
                        expressionStmt.getExpression().asVariableDeclarationExpr(), typeSolver);
            }
            return new NoSymbolDeclarator<>(expressionStmt, typeSolver);
        }
        if (node instanceof ForEachStmt foreachStmt) {
            return new VariableSymbolDeclarator(foreachStmt.getVariable(), typeSolver);
        }
        if (node instanceof ForStmt forStmt) {
            Optional<VariableDeclarationExpr> variableDecl = forStmt.getInitialization().stream()
                    .filter(expr -> expr.isVariableDeclarationExpr())
                    .map(expr -> expr.asVariableDeclarationExpr())
                    .findFirst();
            if (variableDecl.isPresent()) {
                return new VariableSymbolDeclarator(variableDecl.get(), typeSolver);
            }
        }
        return new NoSymbolDeclarator<>(node, typeSolver);
    }
}
