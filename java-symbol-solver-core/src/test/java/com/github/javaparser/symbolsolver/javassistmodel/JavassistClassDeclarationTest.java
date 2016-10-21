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

import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import com.google.common.collect.ImmutableSet;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

public class JavassistClassDeclarationTest extends AbstractTest {

    private TypeSolver typeSolver;

    @Before
    public void setup() throws IOException {
        String pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new JreTypeSolver());
    }

    ///
    /// Test misc
    ///

    @Test
    public void testIsClass() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(true, compilationUnit.isClass());
    }

    @Test
    public void testIsInterface() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isInterface());
    }

    @Test
    public void testIsEnum() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isEnum());
    }

    @Test
    public void testIsTypeVariable() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isTypeParameter());
    }

    @Test
    public void testIsType() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(true, compilationUnit.isType());
    }

    @Test
    public void testAsType() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asType());
    }

    @Test
    public void testAsClass() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asClass());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsInterface() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asInterface();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsEnum() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asEnum();
    }

    @Test
    public void testGetQualifiedName() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.CompilationUnit", compilationUnit.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

    @Test
    public void testGetSuperclass() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().getQualifiedName());
    }

    @Test
    public void testGetAllSuperclasses() {
        JavassistClassDeclaration cu = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllAncestors() {
        JavassistClassDeclaration cu = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllAncestors().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetInterfaces() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        JavassistClassDeclaration coid = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.DocumentableNode"), coid.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllInterfaces() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        JavassistClassDeclaration coid = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.NamedNode", "com.github.javaparser.ast.body.AnnotableNode", "com.github.javaparser.ast.DocumentableNode"), coid.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }
}
