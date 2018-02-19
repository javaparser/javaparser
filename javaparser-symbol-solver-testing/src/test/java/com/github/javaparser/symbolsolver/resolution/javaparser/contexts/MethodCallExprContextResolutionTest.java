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

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParseException;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.core.resolution.Context;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodCallExprContext;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * @author Malte Langkabel
 */
public class MethodCallExprContextResolutionTest extends AbstractResolutionTest {
    private MethodCallExpr getMethodCallExpr(String methodName, String callingMethodName) {
        CompilationUnit cu = parseSample("MethodCalls");

        com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodCalls");
        MethodDeclaration method = Navigator.demandMethod(clazz, methodName);
        return Navigator.findMethodCall(method, callingMethodName).get();
    }

    private CombinedTypeSolver createTypeSolver() {
        File src = adaptPath(new File("src/test/resources"));
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        return combinedTypeSolver;
    }

    @Test
    public void solveNestedMethodCallExprContextWithoutScope() {
        MethodCallExpr methodCallExpr = getMethodCallExpr("bar1", "foo");
        CombinedTypeSolver typeSolver = createTypeSolver();

        Context context = new MethodCallExprContext(methodCallExpr, typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage("foo", Collections.emptyList(), typeSolver);
        assertTrue(ref.isPresent());
        assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
    }

    @Test
    public void solveGenericMethodCallMustUseProvidedTypeArgs() {
        assertCanSolveGenericMethodCallMustUseProvidedTypeArgs("genericMethod0");
    }

    @Test
    public void solveStaticGenericMethodCallMustUseProvidedTypeArgs() {
        assertCanSolveGenericMethodCallMustUseProvidedTypeArgs("staticGenericMethod0");
    }

    private void assertCanSolveGenericMethodCallMustUseProvidedTypeArgs(String callMethodName) {
        MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", callMethodName);
        CombinedTypeSolver typeSolver = createTypeSolver();

        MethodCallExprContext context = new MethodCallExprContext(methodCallExpr, typeSolver);

        Optional<MethodUsage> ref = context.solveMethodAsUsage(callMethodName, Collections.emptyList(), typeSolver);
        assertTrue(ref.isPresent());
        assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
        assertEquals(Collections.singletonList("java.lang.Integer"), ref.get().typeParametersMap().getTypes().stream().map(ty -> ty.asReferenceType().describe()).collect(Collectors.toList()));
    }

    @Test
    public void solveGenericMethodCallCanInferFromArguments() {
        assertCanSolveGenericMethodCallCanInferFromArguments("genericMethod1");
    }

    @Test
    public void solveStaticGenericMethodCallCanInferFromArguments() {
        assertCanSolveGenericMethodCallCanInferFromArguments("staticGenericMethod1");
    }

    private void assertCanSolveGenericMethodCallCanInferFromArguments(String callMethodName) {
        MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", callMethodName);
        CombinedTypeSolver typeSolver = createTypeSolver();

        MethodCallExprContext context = new MethodCallExprContext(methodCallExpr, typeSolver);

        ResolvedReferenceTypeDeclaration stringType = typeSolver.solveType("java.lang.String");

        List<ResolvedType> argumentsTypes = new ArrayList<>();
        argumentsTypes.add(new ReferenceTypeImpl(stringType, typeSolver));

        Optional<MethodUsage> ref = context.solveMethodAsUsage(callMethodName, argumentsTypes, typeSolver);
        assertTrue(ref.isPresent());
        assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
        assertEquals(Collections.singletonList("java.lang.String"), ref.get().typeParametersMap().getTypes().stream().map(ty -> ty.asReferenceType().describe()).collect(Collectors.toList()));
    }
}
