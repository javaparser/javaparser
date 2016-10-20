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

import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import com.github.javaparser.symbolsolver.model.declarations.ValueDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.assertEquals;

/**
 * @author Federico Tomassetti
 */
public class SymbolSolverTest extends AbstractTest {

    private TypeSolver typeSolverNewCode;
    private SymbolSolver symbolSolver;

    @Before
    public void setup() {

        File srcNewCode = adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-core"));
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new JreTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(srcNewCode));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath(new File("src/test/resources/javaparser_new_src/javaparser-generated-sources"))));
        typeSolverNewCode = combinedTypeSolverNewCode;

        symbolSolver = new SymbolSolver(typeSolverNewCode);
    }

    @Test
    public void testSolveSymbolUnexisting() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<? extends ValueDeclaration> res = symbolSolver.solveSymbolInType(constructorDeclaration, "unexisting");
        assertEquals(false, res.isSolved());
    }

    @Test
    public void testSolveSymbolToDeclaredField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<? extends ValueDeclaration> res = symbolSolver.solveSymbolInType(constructorDeclaration, "name");
        assertEquals(true, res.isSolved());
        assertEquals(true, res.getCorrespondingDeclaration().isField());
    }

    @Test
    public void testSolveSymbolToInheritedPublicField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<? extends ValueDeclaration> res = symbolSolver.solveSymbolInType(constructorDeclaration, "NODE_BY_BEGIN_POSITION");
        assertEquals(true, res.isSolved());
        assertEquals(true, res.getCorrespondingDeclaration().isField());
    }

    @Test
    public void testSolveSymbolToInheritedPrivateField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<? extends ValueDeclaration> res = symbolSolver.solveSymbolInType(constructorDeclaration, "parentNode");
        assertEquals(false, res.isSolved());
    }
}
