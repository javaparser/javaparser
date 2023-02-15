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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserConstructorDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ConstructorsResolutionTest extends AbstractResolutionTest {

    @AfterEach
    void resetConfiguration() {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }

    @Test
    void solveNormalConstructor() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testNormalConstructor");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
        ConstructorDeclaration actualConstructor =
                ((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

        ClassOrInterfaceDeclaration otherClazz = Navigator.demandClass(cu, "OtherClass");
        ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(otherClazz, 0);

        assertEquals(expectedConstructor, actualConstructor);
    }

    @Test
    void solveInnerClassConstructor() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testInnerClassConstructor");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(1)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
        ConstructorDeclaration actualConstructor =
                ((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

        ClassOrInterfaceDeclaration innerClazz = Navigator.demandClass(cu, "OtherClass.InnerClass");
        ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(innerClazz, 0);

        assertEquals(expectedConstructor, actualConstructor);
    }

    @Test
    void solveInnerClassConstructorWithNewScope() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testInnerClassConstructorWithNewScope");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
        ConstructorDeclaration actualConstructor =
                ((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

        ClassOrInterfaceDeclaration innerClazz = Navigator.demandClass(cu, "OtherClass.InnerClass");
        ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(innerClazz, 0);

        assertEquals(expectedConstructor, actualConstructor);
    }

    @Test
    void solveInnerInnerClassConstructor() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testInnerInnerClassConstructor");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);
        ConstructorDeclaration actualConstructor =
                ((JavaParserConstructorDeclaration) ref.getCorrespondingDeclaration()).getWrappedNode();

        ClassOrInterfaceDeclaration innerClazz = Navigator.demandClass(cu, "OtherClass.InnerClass.InnerInnerClass");
        ConstructorDeclaration expectedConstructor = Navigator.demandConstructor(innerClazz, 0);

        assertEquals(expectedConstructor, actualConstructor);
    }

    @Test
    void solveAnonymousInnerClassEmptyConstructor() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testAnonymousInnerClassEmptyConstructor");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);

        assertTrue(ref.isSolved());
        assertEquals(0, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    void solveAnonymousInnerClassEmptyConstructorInterface() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testAnonymousInnerClassEmptyConstructorInterface");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);

        assertTrue(ref.isSolved());
        assertEquals(0, ref.getCorrespondingDeclaration().getNumberOfParams());
    }

    @Test
    void solveAnonymousInnerClassStringConstructor() {
        CompilationUnit cu = parseSample("ConstructorCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ConstructorCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, "testAnonymousInnerClassStringConstructor");
        ObjectCreationExpr objectCreationExpr = method.getBody().get().getStatements().get(0)
                .asExpressionStmt().getExpression().asObjectCreationExpr();

        SymbolReference<ResolvedConstructorDeclaration> ref =
                JavaParserFacade.get(new ReflectionTypeSolver()).solve(objectCreationExpr);

        assertTrue(ref.isSolved());
        assertEquals(1, ref.getCorrespondingDeclaration().getNumberOfParams());
        assertEquals("java.lang.String", ref.getCorrespondingDeclaration().getParam(0).getType().describe());
    }

    @Test
    public void testIssue1436() {
        CompilationUnit cu = StaticJavaParser.parse("interface TypeIfc {}" +
                "class TypeA {" +
                "  void doSomething(TypeIfc typeIfc) {" +
                "  }" +
                "}" +

                "class B {" +
                "  void x() {" +
                "    TypeA obj = new TypeA();" +
                "    obj.doSomething(new TypeIfc() {" +
                "    });" +
                "  }" +
                "}");

        List<ObjectCreationExpr> oceList = cu.findAll(ObjectCreationExpr.class);
        assertEquals(2, oceList.size());

        SymbolReference<ResolvedConstructorDeclaration> ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(oceList.get(0)); // new TypeA();
        assertTrue(ref.isSolved());
        assertEquals("TypeA", ref.getCorrespondingDeclaration().declaringType().getQualifiedName());

        ref = JavaParserFacade.get(new ReflectionTypeSolver()).solve(oceList.get(1)); // new TypeIfc() {}
        assertTrue(ref.isSolved());
        //assertEquals("B$1", ref.getCorrespondingDeclaration().declaringType().getQualifiedName());
        assertTrue(ref.getCorrespondingDeclaration().declaringType().getQualifiedName().startsWith("B.Anonymous-"));
    }

    @Test
    void solveEnumConstructor() {
        // configure symbol solver before parsing
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = parseSample("ConstructorCallsEnum");
        EnumDeclaration enumDeclaration = Navigator.demandEnum(cu, "ConstructorCallsEnum");
        ConstructorDeclaration constructor = (ConstructorDeclaration) enumDeclaration.getChildNodes().get(3);

        ResolvedConstructorDeclaration resolvedConstructor = constructor.resolve();

        assertEquals("ConstructorCallsEnum", resolvedConstructor.declaringType().getName());
        assertEquals(1, resolvedConstructor.getNumberOfParams());
        assertEquals("i", resolvedConstructor.getParam(0).getName());
        assertEquals(ResolvedPrimitiveType.INT, resolvedConstructor.getParam(0).getType());
    }

    @Test
    void solveNonPublicParentConstructorReflection() {
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));

        CompilationUnit cu = parseSample("ReflectionTypeSolverConstructorResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "ReflectionTypeSolverConstructionResolution");
        ConstructorDeclaration constructorDeclaration = Navigator.demandConstructor(clazz, 0);
        ExplicitConstructorInvocationStmt stmt =
                (ExplicitConstructorInvocationStmt) constructorDeclaration.getBody().getStatement(0);

        ResolvedConstructorDeclaration cd = stmt.resolve();

        assertEquals(1, cd.getNumberOfParams());
        assertEquals(ResolvedPrimitiveType.INT, cd.getParam(0).getType());
        assertEquals("java.lang.AbstractStringBuilder", cd.declaringType().getQualifiedName());
    }

    @Test
    void testGenericParentContructorJavassist() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javassist_generics/generics.jar");
        TypeSolver typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver(true));
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(typeSolver));

        CompilationUnit cu = parseSample("JarTypeSolverConstructorResolution");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "JarTypeSolverConstructionResolution");
        ConstructorDeclaration constructorDeclaration = Navigator.demandConstructor(clazz, 0);
        ExplicitConstructorInvocationStmt stmt =
                (ExplicitConstructorInvocationStmt) constructorDeclaration.getBody().getStatement(0);

        ResolvedConstructorDeclaration cd = stmt.resolve();

        assertEquals(1, cd.getNumberOfParams());
        assertEquals("S", cd.getParam(0).describeType());
        assertEquals("javaparser.GenericClass", cd.declaringType().getQualifiedName());
    }

}
