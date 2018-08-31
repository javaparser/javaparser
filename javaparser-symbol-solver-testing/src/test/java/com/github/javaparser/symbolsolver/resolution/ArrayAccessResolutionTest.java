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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserFieldDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserSymbolDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.util.Optional;

import static org.junit.Assert.assertEquals;

public class ArrayAccessResolutionTest extends AbstractResolutionTest {

    @Test
    public void resolveArrayField() {
        // configure symbol solver before parsing
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get field access expression
        CompilationUnit cu = parseSample("ArrayAccess");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ArrayAccess");
        MethodDeclaration method = Navigator.demandMethod(clazz, "fieldAccess");

        ReturnStmt returnStmt = (ReturnStmt) method.getBody().get().getStatements().get(0);
        ArrayAccessExpr expression = returnStmt.getExpression().get().asMethodCallExpr().getScope().get()
                                             .asArrayAccessExpr();

        // resolve field access expression
        Optional<ResolvedValueDeclaration> resolvedValueDeclaration = expression.resolveAccessedArray();

        // get expected field declaration
        VariableDeclarator variableDeclarator = Navigator.demandField(clazz, "array");

        // check that the expected field declaration equals the resolved field declaration
        assertEquals(variableDeclarator, ((JavaParserFieldDeclaration) resolvedValueDeclaration.get())
                                                 .getVariableDeclarator());
    }

    @Test
    public void resolveArrayExplicitField() {
        // configure symbol solver before parsing
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get field access expression
        CompilationUnit cu = parseSample("ArrayAccess");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ArrayAccess");
        MethodDeclaration method = Navigator.demandMethod(clazz, "explicitFieldAccess");

        ReturnStmt returnStmt = (ReturnStmt) method.getBody().get().getStatements().get(0);
        ArrayAccessExpr expression = returnStmt.getExpression().get().asArrayAccessExpr();

        // resolve field access expression
        Optional<ResolvedValueDeclaration> resolvedValueDeclaration = expression.resolveAccessedArray();

        // get expected field declaration
        VariableDeclarator variableDeclarator = Navigator.demandField(clazz, "array");

        // check that the expected field declaration equals the resolved field declaration
        assertEquals(variableDeclarator, ((JavaParserFieldDeclaration) resolvedValueDeclaration.get())
                                                 .getVariableDeclarator());
    }

    @Test
    public void resolveLocalArray() {
        // configure symbol solver before parsing
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get field access expression
        CompilationUnit cu = parseSample("ArrayAccess");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ArrayAccess");
        MethodDeclaration method = Navigator.demandMethod(clazz, "localAccess");

        ReturnStmt returnStmt = (ReturnStmt) method.getBody().get().getStatement(1);
        ArrayAccessExpr expression = returnStmt.getExpression().get().asArrayAccessExpr();

        // resolve field access expression
        Optional<ResolvedValueDeclaration> resolvedValueDeclaration = expression.resolveAccessedArray();

        // get expected field declaration
        VariableDeclarator variableDeclarator = method.getBody().get().getStatement(0).asExpressionStmt()
                                                        .getExpression().asVariableDeclarationExpr().getVariable(0);

        // check that the expected field declaration equals the resolved field declaration
        assertEquals(variableDeclarator, ((JavaParserSymbolDeclaration) resolvedValueDeclaration.get())
                                                 .getWrappedNode());
    }

    @Test
    public void resolveLocalEnclosedArray() {
        // configure symbol solver before parsing
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get field access expression
        CompilationUnit cu = parseSample("ArrayAccess");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ArrayAccess");
        MethodDeclaration method = Navigator.demandMethod(clazz, "localEnclosedAccess");

        ReturnStmt returnStmt = (ReturnStmt) method.getBody().get().getStatement(1);
        ArrayAccessExpr expression = returnStmt.getExpression().get().asArrayAccessExpr();

        // resolve field access expression
        Optional<ResolvedValueDeclaration> resolvedValueDeclaration = expression.resolveAccessedArray();

        // get expected field declaration
        VariableDeclarator variableDeclarator = method.getBody().get().getStatement(0).asExpressionStmt()
                                                        .getExpression().asVariableDeclarationExpr().getVariable(0);

        // check that the expected field declaration equals the resolved field declaration
        assertEquals(variableDeclarator, ((JavaParserSymbolDeclaration) resolvedValueDeclaration.get())
                                                 .getWrappedNode());
    }

    @Test
    public void resolveDeclarationLessAccess() {
        // configure symbol solver before parsing
        JavaParser.getStaticConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get field access expression
        CompilationUnit cu = parseSample("ArrayAccess");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ArrayAccess");
        MethodDeclaration method = Navigator.demandMethod(clazz, "declarationLessAccess");

        ReturnStmt returnStmt = (ReturnStmt) method.getBody().get().getStatement(0);
        ArrayAccessExpr expression = returnStmt.getExpression().get().asArrayAccessExpr();

        // resolve field access expression
        Optional<ResolvedValueDeclaration> resolvedValueDeclaration = expression.resolveAccessedArray();

        // check that the expected field declaration equals the resolved field declaration
        assertEquals(Optional.empty(), resolvedValueDeclaration);
    }
}
