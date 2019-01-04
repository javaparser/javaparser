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

package com.github.javaparser.symbolsolver.resolution.javaparser.declarations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserTypeParameter;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
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
        MethodCallExpr callToFoo = (MethodCallExpr) Navigator.findReturnStmt(methodDecl).getExpression().get();
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
        MethodCallExpr callToFoo = (MethodCallExpr) Navigator.findReturnStmt(methodDecl).getExpression().get();
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
