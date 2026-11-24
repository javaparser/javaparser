/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
import static org.junit.jupiter.api.Assertions.assertThrows;

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
 * Method references whose scope has an interface type: the methods of {@code java.lang.Object} are members of every
 * interface (JLS 9.2), so e.g. {@code Runnable::hashCode} and {@code charSequence::equals} resolve.
 */
class MethodReferenceInterfaceScopeTest {

    private static final ReflectionTypeSolver TYPE_SOLVER = new ReflectionTypeSolver();

    private static final String IMPORTS =
            "import java.util.*; import java.util.function.*; import java.util.stream.*; ";

    private static CompilationUnit parse(String code) {
        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(TYPE_SOLVER));
        return new JavaParser(configuration).parse(IMPORTS + code).getResult().get();
    }

    private static MethodUsage resolveAsUsage(String code, ResolvedType... paramTypes) {
        MethodReferenceExpr expr =
                parse(code).findFirst(MethodReferenceExpr.class).get();
        return JavaParserFacade.get(TYPE_SOLVER).toMethodUsage(expr, Arrays.asList(paramTypes));
    }

    private static MethodUsage resolveUnboundAsUsage(String code) {
        MethodReferenceExpr expr =
                parse(code).findFirst(MethodReferenceExpr.class).get();
        ResolvedType receiver = expr.getScope().calculateResolvedType();
        return JavaParserFacade.get(TYPE_SOLVER).toMethodUsage(expr, Arrays.asList(receiver));
    }

    private static String collectType(String code) {
        return parse(code)
                .findFirst(MethodCallExpr.class, c -> c.getNameAsString().equals("collect"))
                .get()
                .calculateResolvedType()
                .describe();
    }

    @Test
    void unboundObjectMethodOfInterface() {
        MethodUsage usage = resolveUnboundAsUsage(
                "class Test { void m() { Function<Runnable, Integer> f = Runnable::hashCode; } }");

        assertEquals("hashCode", usage.getName());
        assertEquals("java.lang.Object", usage.declaringType().getQualifiedName());
    }

    @Test
    void boundObjectMethodOfInterface() {
        ResolvedType object = new com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl(
                TYPE_SOLVER.getSolvedJavaLangObject());

        MethodUsage usage =
                resolveAsUsage("class Test { void m(CharSequence c) { Predicate<Object> p = c::equals; } }", object);

        assertEquals("equals", usage.getName());
        assertEquals("java.lang.Object", usage.declaringType().getQualifiedName());
    }

    @Test
    void methodOfInterfaceIsNotShadowedByObject() {
        MethodUsage usage = resolveUnboundAsUsage(
                "class Test { void m() { ToIntFunction<CharSequence> f = CharSequence::length; } }");

        assertEquals("length", usage.getName());
        assertEquals("java.lang.CharSequence", usage.declaringType().getQualifiedName());
    }

    @Test
    void methodNotInInterfaceIsNotResolved() {
        assertThrows(
                UnsolvedSymbolException.class,
                () -> resolveUnboundAsUsage(
                        "class Test { void m() { Function<Runnable, Integer> f = Runnable::intValue; } }"));
    }

    @Test
    void streamMapWithObjectMethodOfInterface() {
        assertEquals(
                "java.util.List<java.lang.Integer>",
                collectType("class Test { Object m(List<Runnable> l) { "
                        + "return l.stream().map(Runnable::hashCode).collect(Collectors.toList()); } }"));
    }

    @Test
    void streamFilterWithBoundObjectMethodOfInterface() {
        assertEquals(
                "java.util.List<java.lang.CharSequence>",
                collectType("class Test { Object m(List<CharSequence> l, CharSequence c) { "
                        + "return l.stream().filter(c::equals).collect(Collectors.toList()); } }"));
    }
}
