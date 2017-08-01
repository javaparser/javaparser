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

package com.github.javaparser.symbolsolver.reflectionmodel;

import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class ReflectionEnumDeclarationTest extends AbstractTest {

    private TypeSolver typeSolver = new ReflectionTypeSolver(false);

    ///
    /// Test misc
    ///

    @Test
    public void testIsClass() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isClass());
    }

    @Test
    public void testIsInterface() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isInterface());
    }

    @Test
    public void testIsEnum() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isEnum());
    }

    @Test
    public void testIsTypeVariable() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isTypeParameter());
    }

    @Test
    public void testIsType() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isType());
    }

    @Test
    public void testAsType() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asType());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsClass() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        modifier.asClass();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsInterface() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        modifier.asInterface();
    }

    @Test
    public void testAsEnum() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asEnum());
    }

    @Test
    public void testGetPackageName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast", modifier.getPackageName());
    }

    @Test
    public void testGetClassName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("Modifier", modifier.getClassName());
    }

    @Test
    public void testGetQualifiedName() {
        ReflectionEnumDeclaration modifier = (ReflectionEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast.Modifier", modifier.getQualifiedName());
    }

}
