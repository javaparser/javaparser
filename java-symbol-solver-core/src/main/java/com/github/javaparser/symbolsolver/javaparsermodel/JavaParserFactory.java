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
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.*;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.FieldSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.NoSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.ParameterSymbolDeclarator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarators.VariableSymbolDeclarator;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.SymbolDeclarator;

import static com.github.javaparser.symbolsolver.javaparser.Navigator.getParentNode;

public class JavaParserFactory {

    public static Context getContext(Node node, TypeSolver typeSolver) {
        if (node == null) {
            return null;
        } else if (node instanceof CompilationUnit) {
            return new CompilationUnitContext((CompilationUnit) node, typeSolver);
        } else if (node instanceof ForeachStmt) {
            return new ForechStatementContext((ForeachStmt) node, typeSolver);
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
        } else if (node instanceof SwitchEntryStmt) {
            return new SwitchEntryContext((SwitchEntryStmt) node, typeSolver);
        } else if (node instanceof Statement) {
            return new StatementContext((Statement) node, typeSolver);
        } else {
            return getContext(getParentNode(node), typeSolver);
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
                return new NoSymbolDeclarator(node, typeSolver);
            }
        } else if (node instanceof IfStmt) {
            return new NoSymbolDeclarator(node, typeSolver);
        } else if (node instanceof ForeachStmt) {
            ForeachStmt foreachStmt = (ForeachStmt) node;
            return new VariableSymbolDeclarator((VariableDeclarationExpr) (foreachStmt.getVariable()), typeSolver);
        } else {
            return new NoSymbolDeclarator(node, typeSolver);
        }
    }

}
