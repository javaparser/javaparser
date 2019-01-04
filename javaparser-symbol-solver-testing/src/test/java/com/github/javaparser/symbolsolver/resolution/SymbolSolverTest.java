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

package com.github.javaparser.symbolsolver.resolution;

import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
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
    private SymbolSolver symbolSolver;

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
