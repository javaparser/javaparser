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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class VariadicResolutionTest extends AbstractResolutionTest {

	@Test
    void issue7() {
        CompilationUnit cu = parseSample("Generics_issue7");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "SomeCollection");

        MethodDeclaration method = Navigator.demandMethod(clazz, "foo3");

        ReturnStmt stmt = (ReturnStmt) method.getBody().get().getStatements().get(0);
        Expression expression = stmt.getExpression().get();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(new ReflectionTypeSolver());
        ResolvedType type = javaParserFacade.getType(expression);
        assertEquals(true, type.isReferenceType());
        assertEquals(List.class.getCanonicalName(), type.asReferenceType().getQualifiedName());
        assertEquals("java.util.List<java.lang.Long>", type.describe());
    }
	
	@Test
    void methodCallWithReferenceTypeAsVaridicArgumentIsSolved() {
        CompilationUnit cu = parseSample("MethodCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodCalls");

        MethodDeclaration method = Navigator.demandMethod(clazz, "variadicMethod");
        MethodCallExpr callExpr = Navigator.findMethodCall(method, "variadicMethod").get();
        
        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        MethodUsage callee = javaParserFacade.solveMethodAsUsage(callExpr);
        assertEquals("variadicMethod", callee.getName());
    }

    @Test
    void resolveVariadicMethodWithGenericArgument() {
        CompilationUnit cu = parseSample("MethodCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodCalls");

        MethodDeclaration method = Navigator.demandMethod(clazz, "genericMethodTest");
        MethodCallExpr callExpr = Navigator.findMethodCall(method, "variadicWithGenericArg").get();

        TypeSolver typeSolver = new ReflectionTypeSolver();
        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        MethodUsage callee = javaParserFacade.solveMethodAsUsage(callExpr);
        assertEquals("variadicWithGenericArg", callee.getName());
    }

    @Test
    void selectMostSpecificVariadic() {
        CompilationUnit cu = parseSample("MethodCalls");
        ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodCalls");

        MethodDeclaration method = Navigator.demandMethod(clazz, "variadicTest");
        List<MethodCallExpr> calls = method.findAll(MethodCallExpr.class);

        Path src = adaptPath("src/test/resources");
        TypeSolver typeSolver = new CombinedTypeSolver(new ReflectionTypeSolver(), new JavaParserTypeSolver(src, new LeanParserConfiguration()));

        JavaParserFacade javaParserFacade = JavaParserFacade.get(typeSolver);
        MethodUsage call1 = javaParserFacade.solveMethodAsUsage(calls.get(0));
        MethodUsage call2 = javaParserFacade.solveMethodAsUsage(calls.get(1));
        assertEquals("int", call1.returnType().describe());
        assertEquals("void", call2.returnType().describe());
    }

}
