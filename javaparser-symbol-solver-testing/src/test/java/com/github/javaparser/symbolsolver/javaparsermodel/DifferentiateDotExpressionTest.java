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

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class DifferentiateDotExpressionTest extends AbstractResolutionTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath("src/test/resources/differentiate_dot_expressions"), new LeanParserConfiguration()));
        typeSolver = combinedTypeSolver;
    }

    @Test
    void methodCallsFromFieldObjects() {
        ClassOrInterfaceDeclaration clazz = ((JavaParserClassDeclaration) typeSolver.solveType("FieldDotExpressions")).getWrappedNode();
        MethodDeclaration mainMethod = Navigator.demandMethod(clazz, "main");
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodCallExpr firstFieldMethodCall = Navigator.findMethodCall(mainMethod, "firstContainerMethod").get();
        MethodCallExpr secondFieldMethodCall = Navigator.findMethodCall(mainMethod, "secondContainerMethod").get();
        MethodCallExpr thirdFieldMethodCall = Navigator.findMethodCall(mainMethod, "thirdContainerMethod").get();

        assertEquals(true, javaParserFacade.solve(firstFieldMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(secondFieldMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(thirdFieldMethodCall).isSolved());
    }

    @Test
    void staticMethodCallsFromInnerClasses() {
        ClassOrInterfaceDeclaration clazz = ((JavaParserClassDeclaration) typeSolver.solveType("InnerClassDotExpressions")).getWrappedNode();
        MethodDeclaration mainMethod = Navigator.demandMethod(clazz, "main");
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodCallExpr methodCall = Navigator.findMethodCall(mainMethod, "methodCall").get();
        MethodCallExpr innerMethodCall = Navigator.findMethodCall(mainMethod, "innerMethodCall").get();
        MethodCallExpr innerInnerMethodCall = Navigator.findMethodCall(mainMethod, "innerInnerMethodCall").get();

        assertEquals(true, javaParserFacade.solve(methodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(innerMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(innerInnerMethodCall).isSolved());
    }

    @Test
    void staticFieldCallsFromInnerClasses() {
        ClassOrInterfaceDeclaration clazz = ((JavaParserClassDeclaration) typeSolver.solveType("InnerStaticClassFieldDotExpressions")).getWrappedNode();
        MethodDeclaration mainMethod = Navigator.demandMethod(clazz, "main");
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodCallExpr methodCallWithNestedStaticFieldParam = Navigator.findMethodCall(mainMethod, "parseInt").get();

        assertEquals(true, javaParserFacade.solve(methodCallWithNestedStaticFieldParam).isSolved());
    }

    @Test
    void packageStaticMethodCalls() {
        ClassOrInterfaceDeclaration clazz = ((JavaParserClassDeclaration) typeSolver.solveType("PackageDotExpressions")).getWrappedNode();
        MethodDeclaration mainMethod = Navigator.demandMethod(clazz, "main");
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);

        MethodCallExpr staticMethodCall = Navigator.findMethodCall(mainMethod, "staticMethod").get();

        MethodCallExpr methodCall = Navigator.findMethodCall(mainMethod, "methodCall").get();
        MethodCallExpr innerMethodCall = Navigator.findMethodCall(mainMethod, "innerMethodCall").get();
        MethodCallExpr innerInnerMethodCall = Navigator.findMethodCall(mainMethod, "innerInnerMethodCall").get();

        MethodCallExpr firstFieldMethodCall = Navigator.findMethodCall(mainMethod, "firstContainerMethod").get();
        MethodCallExpr secondFieldMethodCall = Navigator.findMethodCall(mainMethod, "secondContainerMethod").get();
        MethodCallExpr thirdFieldMethodCall = Navigator.findMethodCall(mainMethod, "thirdContainerMethod").get();

        assertEquals(true, javaParserFacade.solve(staticMethodCall).isSolved());

        assertEquals(true, javaParserFacade.solve(methodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(innerMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(innerInnerMethodCall).isSolved());

        assertEquals(true, javaParserFacade.solve(firstFieldMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(secondFieldMethodCall).isSolved());
        assertEquals(true, javaParserFacade.solve(thirdFieldMethodCall).isSolved());
    }
}
