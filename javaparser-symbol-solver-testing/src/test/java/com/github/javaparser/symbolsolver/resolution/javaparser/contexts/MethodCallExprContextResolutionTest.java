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

package com.github.javaparser.symbolsolver.resolution.javaparser.contexts;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.Context;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.contexts.MethodCallExprContext;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.Test;

import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Malte Langkabel
 */
class MethodCallExprContextResolutionTest extends AbstractResolutionTest {
	private MethodCallExpr getMethodCallExpr(String methodName, String callingMethodName) {
		CompilationUnit cu = parseSample("MethodCalls");

		com.github.javaparser.ast.body.ClassOrInterfaceDeclaration clazz = Navigator.demandClass(cu, "MethodCalls");
		MethodDeclaration method = Navigator.demandMethod(clazz, methodName);
		return Navigator.findMethodCall(method, callingMethodName).get();
	}

	private CombinedTypeSolver createTypeSolver() {
		Path src = adaptPath("src/test/resources");
		CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
		combinedTypeSolver.add(new ReflectionTypeSolver());
		combinedTypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));
		return combinedTypeSolver;
	}

	@Test
	void solveNestedMethodCallExprContextWithoutScope() {
		MethodCallExpr methodCallExpr = getMethodCallExpr("bar1", "foo");
		CombinedTypeSolver typeSolver = createTypeSolver();

		Context context = new MethodCallExprContext(methodCallExpr, typeSolver);

		Optional<MethodUsage> ref = context.solveMethodAsUsage("foo", Collections.emptyList());
		assertTrue(ref.isPresent());
		assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
	}

	@Test
	void solveGenericMethodCallMustUseProvidedTypeArgs() {
		assertCanSolveGenericMethodCallMustUseProvidedTypeArgs("genericMethod0");
	}

	@Test
	void solveStaticGenericMethodCallMustUseProvidedTypeArgs() {
		assertCanSolveGenericMethodCallMustUseProvidedTypeArgs("staticGenericMethod0");
	}

	private void assertCanSolveGenericMethodCallMustUseProvidedTypeArgs(String callMethodName) {
		MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", callMethodName);
		CombinedTypeSolver typeSolver = createTypeSolver();

		MethodCallExprContext context = new MethodCallExprContext(methodCallExpr, typeSolver);

		Optional<MethodUsage> ref = context.solveMethodAsUsage(callMethodName, Collections.emptyList());
		assertTrue(ref.isPresent());
		assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
		assertEquals(Collections.singletonList("java.lang.Integer"), ref.get().typeParametersMap().getTypes().stream()
				.map(ty -> ty.asReferenceType().describe()).collect(Collectors.toList()));
	}

	@Test
	void solveGenericMethodCallCanInferFromArguments() {
		assertCanSolveGenericMethodCallCanInferFromArguments("genericMethod1");
	}

	@Test
	void solveStaticGenericMethodCallCanInferFromArguments() {
		assertCanSolveGenericMethodCallCanInferFromArguments("staticGenericMethod1");
	}

	private void assertCanSolveGenericMethodCallCanInferFromArguments(String callMethodName) {
		MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", callMethodName);
		CombinedTypeSolver typeSolver = createTypeSolver();

		MethodCallExprContext context = new MethodCallExprContext(methodCallExpr, typeSolver);

		ResolvedReferenceTypeDeclaration stringType = typeSolver.solveType("java.lang.String");

		List<ResolvedType> argumentsTypes = new ArrayList<>();
		argumentsTypes.add(new ReferenceTypeImpl(stringType));

		Optional<MethodUsage> ref = context.solveMethodAsUsage(callMethodName, argumentsTypes);
		assertTrue(ref.isPresent());
		assertEquals("MethodCalls", ref.get().declaringType().getQualifiedName());
		assertEquals(Collections.singletonList("java.lang.String"), ref.get().typeParametersMap().getTypes().stream()
				.map(ty -> ty.asReferenceType().describe()).collect(Collectors.toList()));
	}

	@Test
	public void test() {
		ParserConfiguration config = new ParserConfiguration()
				.setSymbolResolver(new JavaSymbolSolver(createTypeSolver()));
		StaticJavaParser.setConfiguration(config);
		CompilationUnit cu = parseSample("Issue2258");
		List<MethodCallExpr> expressions = cu.getChildNodesByType(MethodCallExpr.class);
		assertEquals(2, expressions.size());
		ResolvedType r = expressions.get(1).calculateResolvedType();
		assertTrue(ResolvedVoidType.class.isAssignableFrom(r.getClass()));
	}

	@Test
	public void testGenericParameter() {
		ParserConfiguration config = new ParserConfiguration()
				.setSymbolResolver(new JavaSymbolSolver(createTypeSolver()));
		StaticJavaParser.setConfiguration(config);
		CompilationUnit cu = parseSample("ISSUES_Generic_Parameter");
		List<MethodCallExpr> expressions = cu.getChildNodesByType(MethodCallExpr.class);
		assertEquals(1, expressions.size());
		ResolvedType r = expressions.get(0).calculateResolvedType();
		assertTrue(ReferenceTypeImpl.class.isAssignableFrom(r.getClass()));
	}

	@Test
	public void testResolveChainedCallOnReflectionType() throws Exception {
		Path pathToJar = adaptPath("src/test/resources/issue2667/jsonobject.jar");

		CombinedTypeSolver typeSolver = createTypeSolver();
		typeSolver.add(new ClassLoaderTypeSolver(new URLClassLoader(new URL[] {pathToJar.toUri().toURL()})));

		ParserConfiguration config = new ParserConfiguration()
				.setSymbolResolver(new JavaSymbolSolver(typeSolver));
		StaticJavaParser.setConfiguration(config);
		CompilationUnit cu = parseSample("Issue2667");
		Set<MethodCallExpr> methodCallExpr = new HashSet<>(cu.findAll(MethodCallExpr.class));

		int errorCount = 0;

		for (MethodCallExpr expr : methodCallExpr) {
			try {
				ResolvedMethodDeclaration rd = expr.resolve();
			} catch (UnsolvedSymbolException e) {
				errorCount++;
			}
		}

		assertEquals(0, errorCount, "Expected zero UnsolvedSymbolException s");
	}
	
	@Test
	void solveVariadicStaticGenericMethodCallCanInferFromArguments() {
		ParserConfiguration config = new ParserConfiguration()
				.setSymbolResolver(new JavaSymbolSolver(createTypeSolver()));
		StaticJavaParser.setConfiguration(config);
		MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", "variadicStaticGenericMethod");

		ResolvedType resolvedType = methodCallExpr.calculateResolvedType();
        assertEquals("java.lang.String", resolvedType.describe());
	}
	
	// Related to issue #3195
	@Test
	void solveVariadicStaticGenericMethodCallCanInferFromArguments2() {
		ParserConfiguration config = new ParserConfiguration()
				.setSymbolResolver(new JavaSymbolSolver(createTypeSolver()));
		StaticJavaParser.setConfiguration(config);
		MethodCallExpr methodCallExpr = getMethodCallExpr("genericMethodTest", "asList");

		ResolvedType resolvedType = methodCallExpr.calculateResolvedType();
        assertEquals("java.util.List<java.lang.String>", resolvedType.describe());
	}
}
