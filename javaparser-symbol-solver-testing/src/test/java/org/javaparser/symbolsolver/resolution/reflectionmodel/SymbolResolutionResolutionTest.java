/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package org.javaparser.symbolsolver.resolution.reflectionmodel;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.body.VariableDeclarator;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.ast.stmt.ReturnStmt;
import org.javaparser.resolution.types.ResolvedType;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
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
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
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
