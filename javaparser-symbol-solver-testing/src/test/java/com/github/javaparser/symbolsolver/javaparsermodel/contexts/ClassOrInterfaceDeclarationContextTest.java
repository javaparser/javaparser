/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ClassOrInterfaceDeclarationContextTest {

    private final TypeSolver typeSolver = new ReflectionTypeSolver();
    private JavaParser javaParser;

    @BeforeEach
    void beforeEach() {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));
        javaParser = new JavaParser();
    }

    @Test
    void testSolveWithoutTypeArguments() {
        CompilationUnit alphaCU = parse("class Alpha { class Foo {} }");
        ClassOrInterfaceDeclaration alpha = Navigator.demandClass(alphaCU, "Alpha");
        ClassOrInterfaceDeclarationContext alphaContext = new ClassOrInterfaceDeclarationContext(alpha, typeSolver);

        assertTrue(alphaContext.solveType("Foo").isSolved());
        assertTrue(alphaContext.solveType("Foo", Collections.emptyList()).isSolved());
        assertFalse(alphaContext.solveType("Foo", Collections.singletonList(ResolvedPrimitiveType.INT)).isSolved());
    }

    @Test
    void testSolveWithTypeArguments() {
        CompilationUnit betaCU = parse("class Beta { class Foo<T> {} }");
        ClassOrInterfaceDeclaration beta = Navigator.demandClassOrInterface(betaCU, "Beta");
        ClassOrInterfaceDeclarationContext betaContext = new ClassOrInterfaceDeclarationContext(beta, typeSolver);

        assertTrue(betaContext.solveType("Foo").isSolved());
        assertFalse(betaContext.solveType("Foo", Collections.emptyList()).isSolved());
        assertTrue(betaContext.solveType("Foo", Collections.singletonList(ResolvedPrimitiveType.INT)).isSolved());
    }

    private CompilationUnit parse(String sourceCode) {
        return javaParser.parse(sourceCode).getResult().orElseThrow(AssertionError::new);
    }

}
