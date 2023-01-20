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

package com.github.javaparser.symbolsolver.javassistmodel;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.model.LambdaArgumentTypePlaceholder;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedWildcard;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.MemoryTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.Pair;
import javassist.ClassPool;
import javassist.CtClass;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.*;

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

    @Nested
    class TestIsAssignableBy {

        private static final String CLASS_TO_SOLVE = "com.github.javaparser.ast.nodeTypes.NodeWithImplements";

        @Test
        void whenNullTypeIsProvided() {
            JavassistInterfaceDeclaration nodeWithImplements = (JavassistInterfaceDeclaration) typeSolver.solveType(CLASS_TO_SOLVE);
            assertTrue(nodeWithImplements.isAssignableBy(NullType.INSTANCE));
        }

        @Test
        void whenLambdaArgumentTypePlaceholderIsProvided() {
            JavassistInterfaceDeclaration nodeWithImplements = (JavassistInterfaceDeclaration) typeSolver.solveType(CLASS_TO_SOLVE);
            assertFalse(nodeWithImplements.isAssignableBy(new LambdaArgumentTypePlaceholder(0)));
        }

        @Test
        void whenEqualTypeIsProvided() {
            JavassistInterfaceDeclaration nodeWithImplements = (JavassistInterfaceDeclaration) typeSolver.solveType(CLASS_TO_SOLVE);
            assertTrue(nodeWithImplements.isAssignableBy(nodeWithImplements));
        }

        @Test
        void whenOtherTypeIsProvided() {
            ResolvedReferenceTypeDeclaration consumer = new ReflectionTypeSolver().solveType(Consumer.class.getCanonicalName());
            JavassistInterfaceDeclaration nodeWithImplements = (JavassistInterfaceDeclaration) typeSolver.solveType(CLASS_TO_SOLVE);
            assertFalse(nodeWithImplements.isAssignableBy(consumer));
        }

        @Test
        void whenSameClassButWithDifferentTypeParametersIsProvided() {
            ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();

            ReferenceTypeImpl javaLangObject = new ReferenceTypeImpl(reflectionTypeSolver.getSolvedJavaLangObject());
            ResolvedWildcard wildCard = ResolvedWildcard.extendsBound(javaLangObject);

            JavassistInterfaceDeclaration nodeWithImplements = (JavassistInterfaceDeclaration) typeSolver.solveType(CLASS_TO_SOLVE);
            ResolvedType typeA = new ReferenceTypeImpl(nodeWithImplements, Collections.singletonList(wildCard));
            ResolvedType typeB = new ReferenceTypeImpl(nodeWithImplements, Collections.singletonList(javaLangObject));

            assertFalse(typeB.isAssignableBy(typeA), "This should not be allowed:" +
                    " NodeWithImplements<Object> node = new NodeWithImplements<? extends Object>()");
            assertTrue(typeA.isAssignableBy(typeB), "This should be allowed:" +
                    " NodeWithImplements<? extends Object> node = new NodeWithImplements<Object>()");
        }

        @Test
        void whenInterfaceIsProvided() {
            MemoryTypeSolver memoryTypeSolver = new MemoryTypeSolver();
            CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver(
                    memoryTypeSolver,
                    new ReflectionTypeSolver()
            );

            ClassPool classPool = new ClassPool();
            CtClass interfaceA = classPool.makeInterface("A");
            CtClass interfaceB = classPool.makeInterface("B", interfaceA);

            JavassistInterfaceDeclaration declarationA = new JavassistInterfaceDeclaration(interfaceA, combinedTypeSolver);
            JavassistInterfaceDeclaration declarationB = new JavassistInterfaceDeclaration(interfaceB, combinedTypeSolver);
            memoryTypeSolver.addDeclaration("A", declarationA);
            memoryTypeSolver.addDeclaration("B", declarationB);

            // Knowing that B extends A we expect:
            assertFalse(declarationA.isAssignableBy(declarationB), "This should not be allowed: B variable = new A()");
            assertTrue(declarationB.isAssignableBy(declarationA), "This should be allowed: A variable = new B()");
        }
    }

    ///
    /// Test ancestors
    ///

    @Test
    void testGetAncestorsWithGenericAncestors() {
        JavassistInterfaceDeclaration compilationUnit = (JavassistInterfaceDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.GenericChildInterface");
        List<ResolvedReferenceType> ancestors = compilationUnit.getAncestors();
        ancestors.sort(new Comparator<ResolvedReferenceType>() {
            @Override
            public int compare(ResolvedReferenceType o1, ResolvedReferenceType o2) {
                return o1.describe().compareTo(o2.describe());
            }
        });
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
