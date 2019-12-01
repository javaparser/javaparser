/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2019 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class JavaSymbolSolverTest extends AbstractResolutionTest {

    @Test
    void resolveMethodDeclaration() {
        TypeSolver typeSolver = new ReflectionTypeSolver();

        CompilationUnit cu = parseSample("SymbolResolverExample");
        new JavaSymbolSolver(typeSolver).inject(cu);

        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMethods().get(0);
        ResolvedMethodDeclaration resolvedMethodDeclaration = methodDeclaration.resolve();
        assertEquals("foo", resolvedMethodDeclaration.getName());
        assertEquals("A[]", resolvedMethodDeclaration.getReturnType().describe());
        assertEquals("java.lang.String[]", resolvedMethodDeclaration.getParam(0).getType().describe());
        assertEquals("int[]", resolvedMethodDeclaration.getParam(1).getType().describe());
    }

    @Test
    void resolveArrayType() {
        TypeSolver typeSolver = new ReflectionTypeSolver();

        CompilationUnit cu = parseSample("SymbolResolverExample");
        new JavaSymbolSolver(typeSolver).inject(cu);

        MethodDeclaration methodDeclaration = cu.getClassByName("A").get().getMethods().get(0);
        ResolvedType resolvedType = methodDeclaration.getType().resolve();
        assertEquals("A[]", resolvedType.describe());
    }
}
