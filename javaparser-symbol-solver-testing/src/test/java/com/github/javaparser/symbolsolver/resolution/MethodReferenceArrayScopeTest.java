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
import com.github.javaparser.ast.expr.MethodReferenceExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

/**
 * Method references whose scope is an array type, e.g. {@code int[]::clone} or {@code String[]::new}
 * (JLS 15.13: ArrayType :: new, ReferenceType :: Identifier).
 */
class MethodReferenceArrayScopeTest {

    private static MethodReferenceExpr parse(String methodReference) {
        ParserConfiguration configuration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        String code = "import java.util.*; class Test { static class Nested { } " + "void m() { Object o = "
                + methodReference + "; } }";
        CompilationUnit cu =
                new JavaParser(configuration).parse(code).getResult().get();
        return cu.findFirst(MethodReferenceExpr.class).get();
    }

    @ParameterizedTest
    @CsvSource(
            delimiter = '|',
            value = {
                "int[]::clone | int[]",
                "int[][]::clone | int[][]",
                "String[]::new | java.lang.String[]",
                "String[][]::new | java.lang.String[][]",
                "java.lang.String[]::new | java.lang.String[]",
                "Nested[]::new | Test.Nested[]",
                "List<String>[]::new | java.util.List<java.lang.String>[]"
            })
    void arrayScopeResolvesToArrayType(String methodReference, String expectedType) {
        MethodReferenceExpr expr = parse(methodReference);
        assertTrue(expr.getScope().isTypeExpr());
        assertTrue(expr.getScope().asTypeExpr().getType().isArrayType());

        ResolvedType scopeType = expr.getScope().calculateResolvedType();

        assertTrue(scopeType.isArray(), methodReference);
        assertEquals(expectedType, scopeType.describe(), methodReference);
    }

    @Test
    void arrayScopeComponentType() {
        ResolvedType scopeType = parse("String[][]::new").getScope().calculateResolvedType();

        assertEquals(
                "java.lang.String[]", scopeType.asArrayType().getComponentType().describe());
    }
}
