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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import java.util.Arrays;
import org.junit.jupiter.api.Test;

/**
 * Method references whose scope is a type variable, e.g. {@code T::compareTo} (JLS 15.13: ReferenceType :: Identifier,
 * where the ReferenceType is a TypeVariable).
 */
class MethodReferenceTypeVariableScopeTest {

    private static final ReflectionTypeSolver TYPE_SOLVER = new ReflectionTypeSolver();

    private static final String IMPORTS =
            "import java.util.*; import java.util.function.*; import java.util.stream.*; ";

    private static MethodReferenceExpr parse(String code) {
        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(TYPE_SOLVER));
        CompilationUnit cu =
                new JavaParser(configuration).parse(IMPORTS + code).getResult().get();
        return cu.findFirst(MethodReferenceExpr.class).get();
    }

    private static MethodCallExpr parseMapCall(String code) {
        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(TYPE_SOLVER));
        CompilationUnit cu =
                new JavaParser(configuration).parse(IMPORTS + code).getResult().get();
        return cu.findFirst(MethodCallExpr.class, c -> c.getNameAsString().equals("map"))
                .get();
    }

    private static void assertTypeVariableScope(MethodReferenceExpr expr, String name) {
        assertTrue(expr.getScope().isTypeExpr());

        ResolvedType scopeType = expr.getScope().calculateResolvedType();

        assertTrue(scopeType.isTypeVariable());
        assertEquals(name, scopeType.asTypeVariable().asTypeParameter().getName());
        assertFalse(expr.isScopePrimaryExpr());
    }

    @Test
    void methodTypeParameter() {
        MethodReferenceExpr expr =
                parse("class Test { <T extends Comparable<T>> void m() { Comparator<T> c = T::compareTo; } }");

        assertTypeVariableScope(expr, "T");
    }

    @Test
    void unboundedMethodTypeParameter() {
        MethodReferenceExpr expr = parse("class Test { <T> void m() { Function<T, String> f = T::toString; } }");

        assertTypeVariableScope(expr, "T");
    }

    @Test
    void classTypeParameter() {
        MethodReferenceExpr expr =
                parse("class Test<T extends Comparable<T>> { void m() { Comparator<T> c = T::compareTo; } }");

        assertTypeVariableScope(expr, "T");
    }

    @Test
    void constructorTypeParameter() {
        MethodReferenceExpr expr =
                parse("class Test { <T extends Number> Test() { Function<T, Integer> f = T::intValue; } }");

        assertTypeVariableScope(expr, "T");
    }

    @Test
    void typeParameterOfEnclosingClassUsedInNestedClass() {
        MethodReferenceExpr expr = parse(
                "class Test<T extends Comparable<T>> { class Inner { void m() { Comparator<T> c = T::compareTo; } } }");

        assertTypeVariableScope(expr, "T");
    }

    @Test
    void multiLetterTypeParameter() {
        MethodReferenceExpr expr =
                parse("class Test { <Elem extends Number> void m() { Function<Elem, Integer> f = Elem::intValue; } }");

        assertTypeVariableScope(expr, "Elem");
    }

    @Test
    void typeParameterShadowingClassName() {
        // the type parameter T hides the class T, so T::hashCode refers to the type variable
        MethodReferenceExpr expr =
                parse("class T { } class Test { <T> void m() { Function<T, Integer> f = T::hashCode; } }");

        assertTypeVariableScope(expr, "T");
    }

    /** Resolves the method with the receiver (the scope type) as first function parameter, followed by extraParams. */
    private static MethodUsage resolveAsUsage(MethodReferenceExpr expr, ResolvedType... extraParams) {
        ResolvedType receiver = expr.getScope().calculateResolvedType();
        ResolvedType[] all = new ResolvedType[extraParams.length + 1];
        all[0] = receiver;
        System.arraycopy(extraParams, 0, all, 1, extraParams.length);
        return JavaParserFacade.get(TYPE_SOLVER).toMethodUsage(expr, Arrays.asList(all));
    }

    @Test
    void resolvesMethodOfBound() {
        MethodReferenceExpr expr =
                parse("class Test { <T extends Number> void m() { Function<T, Integer> f = T::intValue; } }");

        MethodUsage usage = resolveAsUsage(expr);

        assertEquals("intValue", usage.getName());
        assertEquals("java.lang.Number", usage.declaringType().getQualifiedName());
    }

    @Test
    void resolvesMethodOfParameterizedBound() {
        MethodReferenceExpr expr =
                parse("class Test { <T extends Comparable<T>> void m() { Comparator<T> c = T::compareTo; } }");

        MethodUsage usage = resolveAsUsage(expr, expr.getScope().calculateResolvedType());

        assertEquals("compareTo", usage.getName());
        assertEquals("java.lang.Comparable", usage.declaringType().getQualifiedName());
    }

    @Test
    void resolvesObjectMethodOfUnboundedTypeVariable() {
        MethodReferenceExpr expr = parse("class Test { <T> void m() { Function<T, String> f = T::toString; } }");

        MethodUsage usage = resolveAsUsage(expr);

        assertEquals("toString", usage.getName());
        assertEquals("java.lang.Object", usage.declaringType().getQualifiedName());
    }

    @Test
    void resolvesMethodsOfEveryBoundOfIntersection() {
        String code = "class Test { <T extends Number & Comparable<T>> void m() { %s f = T::%s; } }";
        MethodReferenceExpr intValue = parse(String.format(code, "Function<T, Integer>", "intValue"));
        MethodReferenceExpr compareTo = parse(String.format(code, "Comparator<T>", "compareTo"));

        MethodUsage intValueUsage = resolveAsUsage(intValue);
        MethodUsage compareToUsage =
                resolveAsUsage(compareTo, compareTo.getScope().calculateResolvedType());

        assertEquals("java.lang.Number", intValueUsage.declaringType().getQualifiedName());
        assertEquals("java.lang.Comparable", compareToUsage.declaringType().getQualifiedName());
    }

    @Test
    void resolvesMethodOfBoundThatIsAnotherTypeVariable() {
        MethodReferenceExpr expr = parse(
                "class Test { <U extends Number, T extends U> void m() { Function<T, Integer> f = T::intValue; } }");

        MethodUsage usage = resolveAsUsage(expr);

        assertEquals("java.lang.Number", usage.declaringType().getQualifiedName());
        assertEquals("intValue", usage.getName());
    }

    @Test
    void methodNotInBoundIsNotResolved() {
        MethodReferenceExpr expr =
                parse("class Test { <T extends Number> void m() { Function<T, Integer> f = T::length; } }");

        assertThrows(UnsolvedSymbolException.class, () -> resolveAsUsage(expr));
    }

    @Test
    void streamMapWithTypeVariableScopeBoundedByNumber() {
        MethodCallExpr call = parseMapCall(
                "class Test { <T extends Number> Stream<Integer> m(List<T> l) { return l.stream().map(T::intValue); } }");

        assertEquals(
                "java.util.stream.Stream<java.lang.Integer>",
                call.calculateResolvedType().describe());
    }

    @Test
    void streamMapWithTypeVariableScopeBoundedByCollection() {
        MethodCallExpr call = parseMapCall(
                "class Test { <T extends Collection<String>> Stream<Integer> m(List<T> l) { return l.stream().map(T::size); } }");

        assertEquals(
                "java.util.stream.Stream<java.lang.Integer>",
                call.calculateResolvedType().describe());
    }

    @Test
    void streamMapWithTypeVariableScopeUsingObjectMethod() {
        MethodCallExpr call =
                parseMapCall("class Test { <T> Stream<String> m(List<T> l) { return l.stream().map(T::toString); } }");

        assertEquals(
                "java.util.stream.Stream<java.lang.String>",
                call.calculateResolvedType().describe());
    }

    @Test
    void typeVariableScopeIsNotAnExpression() {
        // A variable named like the type variable is an expression and must not be treated as a type
        // This is currently not handled correctly.
        assertThrows(
                AssertionError.class,
                () -> {
                    MethodReferenceExpr expr =
                            parse("class Test { <T> void m(String T) { Supplier<Integer> f = T::length; } }");

                    assertFalse(expr.getScope().isTypeExpr()
                            && expr.getScope().calculateResolvedType().isTypeVariable());
                    assertTrue(expr.isScopePrimaryExpr());
                },
                "This bug has been fixed! Remove this assertThrows block.");
    }
}
