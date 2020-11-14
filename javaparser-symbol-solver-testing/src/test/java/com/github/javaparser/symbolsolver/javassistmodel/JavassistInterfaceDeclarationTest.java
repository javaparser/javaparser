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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.Pair;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;

class JavassistInterfaceDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver;

    private TypeSolver anotherTypeSolver;

    @BeforeEach
    void setup() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-3.0.0-alpha.2.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());

        Path anotherPathToJar = adaptPath("src/test/resources/test-artifact-1.0.0.jar");
        anotherTypeSolver = new CombinedTypeSolver(new JarTypeSolver(anotherPathToJar), new ReflectionTypeSolver());
    }

    ///
    /// Test misc
    ///

    @Test
    void testIsClass() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(false, nodeWithAnnotations.isClass());
    }

    @Test
    void testIsInterface() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(true, nodeWithAnnotations.isInterface());
    }

    @Test
    void testIsEnum() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(false, nodeWithAnnotations.isEnum());
    }

    @Test
    void testIsTypeVariable() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(false, nodeWithAnnotations.isTypeParameter());
    }

    @Test
    void testIsType() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(true, nodeWithAnnotations.isType());
    }

    @Test
    void testAsType() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(nodeWithAnnotations, nodeWithAnnotations.asType());
    }

    @Test
    void testAsClass() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        nodeWithAnnotations.asClass();
    });
}

    @Test
    void testAsInterface() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals(nodeWithAnnotations, nodeWithAnnotations.asInterface());
    }

    @Test
    void testAsEnum() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        nodeWithAnnotations.asEnum();
    });
}

    @Test
    void testGetPackageName() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals("com.github.javaparser.ast.nodeTypes", nodeWithAnnotations.getPackageName());
    }

    @Test
    void testGetClassName() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals("NodeWithAnnotations", nodeWithAnnotations.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        JavassistInterfaceDeclaration nodeWithAnnotations = (JavassistInterfaceDeclaration) typeSolver.solveType("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations");
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", nodeWithAnnotations.getQualifiedName());
    }

    @Test
    void testHasDirectlyAnnotation(){
        JavassistInterfaceDeclaration compilationUnit = (JavassistInterfaceDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.TestInterface");
        assertTrue(compilationUnit.hasDirectlyAnnotation("com.github.javaparser.test.TestAnnotation"));
    }

    @Test
    void testHasAnnotation(){
        JavassistInterfaceDeclaration compilationUnit = (JavassistInterfaceDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.TestChildInterface");
        assertTrue(compilationUnit.hasAnnotation("com.github.javaparser.test.TestAnnotation"));
    }

    ///
    /// Test ancestors
    ///

    @Test
    void testGetAncestorsWithGenericAncestors() {
        JavassistInterfaceDeclaration compilationUnit = (JavassistInterfaceDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.GenericChildInterface");
        List<ResolvedReferenceType> ancestors = compilationUnit.getAncestors();
        assertEquals(2, ancestors.size());
        assertEquals("com.github.javaparser.test.GenericInterface<S>", ancestors.get(0).describe()); // Type should be 'S', from the GenericChildInterface
        assertEquals("java.lang.Object", ancestors.get(1).describe());

        // check the ancestor generic type is mapped to the type of the child
        List<Pair<ResolvedTypeParameterDeclaration, ResolvedType>> typePamatersMap = ancestors.get(0).getTypeParametersMap();
        assertEquals(1, typePamatersMap.size());

        ResolvedTypeParameterDeclaration genericTypeParameterDeclaration = typePamatersMap.get(0).a;
        assertEquals("com.github.javaparser.test.GenericInterface.T", genericTypeParameterDeclaration.getQualifiedName());
        ResolvedType genericResolvedType = typePamatersMap.get(0).b;
        assertEquals("com.github.javaparser.test.GenericChildInterface.S", genericResolvedType.asTypeParameter().getQualifiedName());
    }

}
