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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.Solver;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Federico Tomassetti
 */
class SymbolSolverTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolverNewCode;
    private Solver symbolSolver;

    @BeforeEach
    void setup() {
        Path srcNewCode = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new ReflectionTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(srcNewCode, new LeanParserConfiguration()));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"), new LeanParserConfiguration()));
        typeSolverNewCode = combinedTypeSolverNewCode;

        symbolSolver = new SymbolSolver(typeSolverNewCode);
    }

    @Test
    void testSolveSymbolUnexisting() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<? extends ResolvedValueDeclaration> res = symbolSolver.solveSymbolInType(constructorDeclaration, "unexisting");
        assertFalse(res.isSolved());
    }

    @Test
    void testSolveSymbolToDeclaredField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<? extends ResolvedValueDeclaration> res = symbolSolver.solveSymbolInType(constructorDeclaration, "name");
        assertTrue(res.isSolved());
        assertTrue(res.getCorrespondingDeclaration().isField());
    }

    @Test
    void testSolveSymbolToInheritedPublicField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<? extends ResolvedValueDeclaration> res = symbolSolver.solveSymbolInType(constructorDeclaration, "NODE_BY_BEGIN_POSITION");
        assertTrue(res.isSolved());
        assertTrue(res.getCorrespondingDeclaration().isField());
    }

    @Test
    void testSolveSymbolToInheritedPrivateField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<? extends ResolvedValueDeclaration> res = symbolSolver.solveSymbolInType(constructorDeclaration, "parentNode");
        assertFalse(res.isSolved());
    }

    @Test
    void testSolvePackageLocalClass() {
        assertTrue(typeSolverNewCode.solveType("com.github.javaparser.FooClass").isClass());
    }
}
