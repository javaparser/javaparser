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

package com.github.javaparser.symbolsolver.resolution.reflectionmodel;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class SymbolResolutionResolutionTest extends AbstractResolutionTest {

    @Test
    void getTypeOfField() {
        CompilationUnit cu = parseSample("ReflectionFieldOfItself");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        VariableDeclarator field = Navigator.demandField(clazz, "PUBLIC");

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType ref = JavaParserFacade.get(typeSolver).getType(field);
        assertEquals("int", ref.describe());
    }

    @Test
    void getTypeOfFieldAccess() {
        CompilationUnit cu = parseSample("ReflectionFieldOfItself");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        VariableDeclarator field = Navigator.demandField(clazz, "PUBLIC");

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType ref = JavaParserFacade.get(typeSolver).getType(field.getInitializer().get());
        assertEquals("int", ref.describe());
    }

    @Test
    void conditionalExpressionExample() {
        CompilationUnit cu = parseSample("JreConditionalExpression");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo1");
        ReturnStmt returnStmt = Navigator.findReturnStmt(method);
        Expression expression = returnStmt.getExpression().get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType ref = JavaParserFacade.get(typeSolver).getType(expression);
        assertEquals("java.lang.String", ref.describe());
    }

    @Test
    void conditionalExpressionExampleFollowUp1() {
        CompilationUnit cu = parseSample("JreConditionalExpression");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MyClass");
        MethodDeclaration method = Navigator.demandMethod(clazz, "foo1");
        MethodCallExpr expression = Navigator.findMethodCall(method, "next").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ResolvedType ref = JavaParserFacade.get(typeSolver).getType(expression);
        assertEquals("java.lang.String", ref.describe());
    }

}
