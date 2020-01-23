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

package org.javaparser.symbolsolver.resolution.javaparser.declarations;

import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.javaparser.ast.body.MethodDeclaration;
import org.javaparser.ast.expr.MethodCallExpr;
import org.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import org.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import org.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import org.javaparser.symbolsolver.javaparser.Navigator;
import org.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import org.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import org.javaparser.symbolsolver.model.resolution.TypeSolver;
import org.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserTypeParameterResolutionTest extends AbstractResolutionTest {

    private void testGenericArguments(String containingMethodName) {
        CompilationUnit cu = parseSample("GenericMethodArguments");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        ClassOrInterfaceDeclaration classDecl = Navigator.demandClass(cu, "GenericMethodArguments");
        MethodDeclaration containingMethod = Navigator.demandMethod(classDecl, containingMethodName);
        MethodCallExpr bar = Navigator.findMethodCall(containingMethod, "apply").get();

        assertTrue(javaParserFacade.solve(bar).isSolved());
    }

    @Test
    void genericMethodWithGenericClassBasedArgument() {
        testGenericArguments("useCase1");
    }

    @Test
    void genericMethodWithGenericClassArgument() {
        testGenericArguments("useCase2");
    }

    @Test
    void declaredOnMethodPositiveCase() {
        CompilationUnit cu = parseSample("MethodTypeParameter");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        ClassOrInterfaceDeclaration classDecl = Navigator.demandClass(cu, "Foo");
        MethodDeclaration methodDecl = Navigator.demandMethod(classDecl, "usage");
        MethodCallExpr callToFoo = (MethodCallExpr) Navigator.demandReturnStmt(methodDecl).getExpression().get();
        ResolvedMethodDeclaration methodDeclaration = javaParserFacade.solve(callToFoo).getCorrespondingDeclaration();
        for (ResolvedTypeParameterDeclaration tp : methodDeclaration.getTypeParameters()) {
            assertTrue(tp instanceof JavaParserTypeParameter);
            assertEquals("C", tp.getName());
            assertEquals(true, tp.declaredOnMethod());
            assertEquals(false, tp.declaredOnType());
        }
    }

    @Test
    void declaredOnMethodNegativeCase() {
        CompilationUnit cu = parseSample("ClassTypeParameter");
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        ClassOrInterfaceDeclaration classDecl = Navigator.demandClass(cu, "Foo");
        MethodDeclaration methodDecl = Navigator.demandMethod(classDecl, "usage");
        MethodCallExpr callToFoo = (MethodCallExpr) Navigator.demandReturnStmt(methodDecl).getExpression().get();
        ResolvedMethodDeclaration methodDeclaration = javaParserFacade.solve(callToFoo).getCorrespondingDeclaration();
        ResolvedReferenceTypeDeclaration typeDeclaration = methodDeclaration.declaringType();
        assertEquals(2, typeDeclaration.getTypeParameters().size());
        assertTrue(typeDeclaration.getTypeParameters().get(0) instanceof JavaParserTypeParameter);
        assertEquals("A", typeDeclaration.getTypeParameters().get(0).getName());
        assertEquals(false, typeDeclaration.getTypeParameters().get(0).declaredOnMethod());
        assertEquals(true, typeDeclaration.getTypeParameters().get(0).declaredOnType());
        assertTrue(typeDeclaration.getTypeParameters().get(1) instanceof JavaParserTypeParameter);
        assertEquals("B", typeDeclaration.getTypeParameters().get(1).getName());
        assertEquals(false, typeDeclaration.getTypeParameters().get(1).declaredOnMethod());
        assertEquals(true, typeDeclaration.getTypeParameters().get(1).declaredOnType());

    }

}
