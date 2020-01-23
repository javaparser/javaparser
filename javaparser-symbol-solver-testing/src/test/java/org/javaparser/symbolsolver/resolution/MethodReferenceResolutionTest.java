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

package org.javaparser.symbolsolver.resolution;

import org.javaparser.StaticJavaParser;
import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.expr.MethodReferenceExpr;
import org.javaparser.ast.stmt.ReturnStmt;
import org.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import org.javaparser.symbolsolver.JavaSymbolSolver;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class MethodReferenceResolutionTest extends AbstractResolutionTest {

    @Test
    void classMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "classMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.Object.hashCode()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void superclassMethodNotOverridden() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "superclassMethodNotOverridden");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.Object.hashCode()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void superclassMethodOverridden() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "superclassMethodOverridden");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.String.hashCode()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void superclassMethodWithSubclassType() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "superclassMethodWithSubclassType");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.Object.hashCode()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Disabled
    @Test
    void fieldAccessMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "fieldAccessMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.lang.PrintStream.println()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void thisClassMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "thisClassMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("MethodReferences.print(java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void superclassMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "superclassMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.print(java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Disabled
    @Test
    void instanceMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "instanceMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("java.util.AbstractList.add()", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void staticMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "staticMethod");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.print(java.lang.Boolean)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void biFunction() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "biFunction");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.isEqualAsStrings(java.lang.Integer, java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void customTriFunction() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "customTriFunction");
        ReturnStmt returnStmt = Navigator.demandReturnStmt(method);
        MethodReferenceExpr methodReferenceExpr = (MethodReferenceExpr) returnStmt.getExpression().get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.getOneNumberAsString(java.lang.Integer, java.lang.Integer, java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void consumerDeclaredInMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "consumerDeclaredInMethod");
        MethodReferenceExpr methodReferenceExpr = method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("MethodReferences.print(java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void functionDeclaredInMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "functionDeclaredInMethod");
        MethodReferenceExpr methodReferenceExpr = method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.returnSameValue(java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void biFunctionDeclaredInMethod() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "biFunctionDeclaredInMethod");
        MethodReferenceExpr methodReferenceExpr = method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.isEqual(java.lang.Integer, java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void consumerUsedInStream() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "consumerUsedInStream");
        MethodReferenceExpr methodReferenceExpr = method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.print(java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void functionUsedInStream() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "functionUsedInStream");
        MethodReferenceExpr methodReferenceExpr = method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.returnSameValue(java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void biFunctionUsedInStream() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "biFunctionUsedInStream");
        MethodReferenceExpr methodReferenceExpr = method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.add(java.lang.Integer, java.lang.Integer)", resolvedMethodDeclaration.getQualifiedSignature());
    }

    @Test
    void biFunctionInMethodCall() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        // parse compilation unit and get method reference expression
        CompilationUnit cu = parseSample("MethodReferences");
        org.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodReferences");
        MethodDeclaration method = Navigator.demandMethod(clazz, "biFunctionInMethodCall");
        MethodReferenceExpr methodReferenceExpr = method.findFirst(MethodReferenceExpr.class).get();

        // resolve method reference expression
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodReferenceExpr.resolve();

        // check that the expected method declaration equals the resolved method declaration
        assertEquals("SuperClass.isEqualAsStrings(java.lang.Integer, java.lang.String)", resolvedMethodDeclaration.getQualifiedSignature());
    }

}
