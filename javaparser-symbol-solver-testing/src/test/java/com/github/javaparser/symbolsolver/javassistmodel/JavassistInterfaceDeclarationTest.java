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

import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class JavassistInterfaceDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver;

    private TypeSolver anotherTypeSolver;

    @Before
    public void setup() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-3.0.0-alpha.2.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());

        Path anotherPathToJar = adaptPath("src/test/resources/test-artifact-1.0.0.jar");
        anotherTypeSolver = new CombinedTypeSolver(new JarTypeSolver(anotherPathToJar), new ReflectionTypeSolver());
    }

    ///
    /// Test misc
    ///

    @Test
    public void testIsClass() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(false, nodeWithAnnotations.isClass());
    }

    @Test
    public void testIsInterface() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(true, nodeWithAnnotations.isInterface());
    }

    @Test
    public void testIsEnum() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(false, nodeWithAnnotations.isEnum());
    }

    @Test
    public void testIsTypeVariable() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(false, nodeWithAnnotations.isTypeParameter());
    }

    @Test
    public void testIsType() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(true, nodeWithAnnotations.isType());
    }

    @Test
    public void testAsType() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(nodeWithAnnotations, nodeWithAnnotations.asType());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsClass() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        nodeWithAnnotations.asClass();
    }

    @Test
    public void testAsInterface() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(nodeWithAnnotations, nodeWithAnnotations.asInterface());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsEnum() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        nodeWithAnnotations.asEnum();
    }

    @Test
    public void testGetPackageName() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals("com.github.javaparser.ast.nodeTypes", nodeWithAnnotations.getPackageName());
    }

    @Test
    public void testGetClassName() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals("NodeWithAnnotations", nodeWithAnnotations.getClassName());
    }

    @Test
    public void testGetQualifiedName() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", nodeWithAnnotations.getQualifiedName());
    }

    @Test
    public void testHasDirectlyAnnotation(){
        JavassistInterfaceDeclaration compilationUnit = (JavassistInterfaceDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.TestInterface");
        assertTrue(compilationUnit.hasDirectlyAnnotation("com.github.javaparser.test.TestAnnotation"));
    }

    @Test
    public void testHasAnnotation(){
        JavassistInterfaceDeclaration compilationUnit = (JavassistInterfaceDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.TestChildInterface");
        assertTrue(compilationUnit.hasAnnotation("com.github.javaparser.test.TestAnnotation"));
    }

    ///
    /// Test ancestors
    ///
}
