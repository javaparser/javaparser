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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.declarations.ResolvedEnumDeclaration;
import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.assertEquals;

public class JavassistEnumDeclarationTest extends AbstractTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() throws IOException {
        String pathToJar = adaptPath("src/test/resources/javaparser-core-3.0.0-alpha.2.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());
    }

    ///
    /// Test misc
    ///

    @Test
    public void testIsClass() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isClass());
    }

    @Test
    public void testIsInterface() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isInterface());
    }

    @Test
    public void testIsEnum() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isEnum());
    }

    @Test
    public void testIsTypeVariable() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isTypeParameter());
    }

    @Test
    public void testIsType() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isType());
    }

    @Test
    public void testAsType() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asType());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsClass() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        modifier.asClass();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsInterface() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        modifier.asInterface();
    }

    @Test
    public void testAsEnum() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asEnum());
    }

    @Test
    public void testGetPackageName() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast", modifier.getPackageName());
    }

    @Test
    public void testGetClassName() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("Modifier", modifier.getClassName());
    }

    @Test
    public void testGetQualifiedName() {
        ResolvedEnumDeclaration modifier = (ResolvedEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast.Modifier", modifier.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

}
