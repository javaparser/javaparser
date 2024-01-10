/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.Solver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.SymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;

class JavaParserFacadeTest extends AbstractResolutionTest {

    private final Solver symbolSolver = new SymbolSolver(new ReflectionTypeSolver());

    @Test
    void classToResolvedType_givenPrimitiveShouldBeAReflectionPrimitiveDeclaration() {
        ResolvedType resolvedType = symbolSolver.classToResolvedType(int.class);
        assertEquals(int.class.getCanonicalName(), resolvedType.describe());
    }

    @Test
    void classToResolvedType_givenClassShouldBeAReflectionClassDeclaration() {
        ResolvedType resolvedType = symbolSolver.classToResolvedType(String.class);
        assertEquals(String.class.getCanonicalName(), resolvedType.describe());
    }

    @Test
    void classToResolvedType_givenClassShouldBeAReflectionInterfaceDeclaration() {
        ResolvedType resolvedType = symbolSolver.classToResolvedType(String.class);
        assertEquals(String.class.getCanonicalName(), resolvedType.describe());
    }

    @Test
    void classToResolvedType_givenEnumShouldBeAReflectionEnumDeclaration() {
        ResolvedType resolvedType = symbolSolver.classToResolvedType(TestEnum.class);
        assertEquals(TestEnum.class.getCanonicalName(), resolvedType.describe());
    }

    @Test
    void classToResolvedType_givenAnnotationShouldBeAReflectionAnnotationDeclaration() {
        ResolvedType resolvedType = symbolSolver.classToResolvedType(Override.class);
        assertEquals(Override.class.getCanonicalName(), resolvedType.describe());
    }

    /**
     * Enum to be tested in {@link JavaParserFacadeTest#classToResolvedType_givenEnumShouldBeAReflectionEnumDeclaration}.
     */
    private enum TestEnum {
        A, B;
    }

    // issue 3939
    @Test
    public void checksThatTheBehaviourIsConsistentInTheEventOfAnUnsolvedSymbol() {
		String code =
				"import java.util.List;\n"
				+ "import java.util.stream.Collectors;\n"
				+ "\n"
				+ "public class Foo {\n"
				+ "\n"
				+ "    void m(List<Class<?>> classNames) {\n"
				+ "        classNames.stream().map(c -> c.asSubclass(IMutator.class));\n"
				+ "    }\n"
				+ "}";
		CompilationUnit cu = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver())).parse(code);
		MethodCallExpr expr = cu.findFirst(MethodCallExpr.class).get();
		// First pass, there must be an UnsolvedSymbolException because the type of the method parameter cannot be resolved
		assertThrows(UnsolvedSymbolException.class, () -> expr.getSymbolResolver().calculateType(expr));
		// Second pass, we always want an exception to ensure consistent behaviour
		assertThrows(UnsolvedSymbolException.class, () -> expr.getSymbolResolver().calculateType(expr));
    }

}
