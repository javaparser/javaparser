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
