/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Collections;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

/**
 * Method references whose scope is an array type, e.g. {@code int[]::clone} or {@code String[]::new}
 * (JLS 15.13: ArrayType :: new, ReferenceType :: Identifier).
 */
class MethodReferenceArrayScopeTest {

    private static CompilationUnit parseUnit(String body) {
        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        String code = "import java.util.*;\n" + "import java.util.function.*;\n"
                + "import java.util.stream.*;\n"
                + "class Test {\n"
                + "    static class Nested { } "
                + body
                + " }";
        return new JavaParser(configuration).parse(code).getResult().get();
    }

    /** Parses {@code methodReference} assigned to a variable of the functional interface type {@code target}. */
    private static MethodReferenceExpr parse(String target, String methodReference) {
        return parseUnit("void m() { " + target + " f = " + methodReference + "; }")
                .findFirst(MethodReferenceExpr.class)
                .get();
    }

    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "Function<int[], int[]> | int[]::clone | int[]",
                "Function<int[][], int[][]> | int[][]::clone | int[][]",
                "IntFunction<String[]> | String[]::new | java.lang.String[]",
                "IntFunction<String[][]> | String[][]::new | java.lang.String[][]",
                "IntFunction<String[]> | java.lang.String[]::new | java.lang.String[]",
                "IntFunction<Nested[]> | Nested[]::new | Test.Nested[]",
                "Function<List<String>[], List<String>[]> | List<String>[]::clone | java.util.List<java.lang.String>[]"
            })
    void arrayScopeResolvesToArrayType(String target, String methodReference, String expectedType) {
        MethodReferenceExpr expr = parse(target, methodReference);
        assertTrue(expr.getScope().isTypeExpr());
        assertTrue(expr.getScope().asTypeExpr().getType().isArrayType());

        ResolvedType scopeType = expr.getScope().calculateResolvedType();

        assertTrue(scopeType.isArray(), methodReference);
        assertEquals(expectedType, scopeType.describe(), methodReference);
    }

    @Test
    void arrayScopeComponentType() {
        ResolvedType scopeType =
                parse("IntFunction<String[][]>", "String[][]::new").getScope().calculateResolvedType();

        assertEquals(
                "java.lang.String[]", scopeType.asArrayType().getComponentType().describe());
    }

    private static MethodUsage resolveUnbound(MethodReferenceExpr expr) {
        ResolvedType receiver = expr.getScope().calculateResolvedType();
        return JavaParserFacade.get(new ReflectionTypeSolver())
                .toMethodUsage(expr, Collections.singletonList(receiver));
    }

    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "Function<int[], int[]> | int[]::clone | int[]",
                "Function<int[][], int[][]> | int[][]::clone | int[][]",
                "Function<String[], String[]> | String[]::clone | java.lang.String[]"
            })
    void cloneOfArrayReturnsTheArrayType(String target, String methodReference, String expectedReturnType) {
        MethodUsage usage = resolveUnbound(parse(target, methodReference));

        assertEquals("clone", usage.getName());
        assertEquals(expectedReturnType, usage.returnType().describe(), methodReference);
    }

    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "ToIntFunction<int[]> | int[]::hashCode",
                "Function<String[], String> | String[]::toString",
                "Function<int[], Class<?>> | int[]::getClass"
            })
    void arrayHasTheMethodsOfObject(String target, String methodReference) {
        MethodReferenceExpr expr = parse(target, methodReference);

        MethodUsage usage = resolveUnbound(expr);

        assertEquals(expr.getIdentifier(), usage.getName());
        assertEquals("java.lang.Object", usage.declaringType().getQualifiedName());
    }

    // End-to-end: type of a call whose argument is a method reference with an array scope.

    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "Stream<int[]> s | s.map(int[]::clone) | java.util.stream.Stream<int[]>",
                "Stream<String[]> s | s.map(String[]::clone) | java.util.stream.Stream<java.lang.String[]>",
                "Stream<int[]> s | s.map(int[]::hashCode) | java.util.stream.Stream<java.lang.Integer>",
                "Stream<String> s | s.toArray(String[]::new) | java.lang.String[]"
            })
    void streamCallWithArrayScopeMethodReference(String declaration, String call, String expectedType) {
        MethodCallExpr expr = parseUnit("void m(" + declaration + ") { var r = " + call + "; }")
                .findAll(MethodCallExpr.class, c -> c.toString().equals(call))
                .get(0);

        assertEquals(expectedType, expr.calculateResolvedType().describe());
    }
}
