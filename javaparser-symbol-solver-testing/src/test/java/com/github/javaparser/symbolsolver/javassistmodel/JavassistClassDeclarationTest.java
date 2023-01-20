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

import com.github.javaparser.ast.Node;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.AssociableToAST;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.LambdaArgumentTypePlaceholder;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclaration;
import com.github.javaparser.symbolsolver.logic.AbstractClassDeclarationTest;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableSet;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.NotFoundException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.*;

class JavassistClassDeclarationTest extends AbstractClassDeclarationTest {

    private TypeSolver typeSolver;

    private TypeSolver newTypeSolver;

    private TypeSolver anotherTypeSolver;

    @BeforeEach
    void setup() throws IOException {
        Path pathToJar = adaptPath("src/test/resources/javaparser-core-2.1.0.jar");
        typeSolver = new CombinedTypeSolver(new JarTypeSolver(pathToJar), new ReflectionTypeSolver());

        Path newPathToJar = adaptPath("src/test/resources/javaparser-core-3.0.0-alpha.2.jar");
        newTypeSolver = new CombinedTypeSolver(new JarTypeSolver(newPathToJar), new ReflectionTypeSolver());

        Path anotherPathToJar = adaptPath("src/test/resources/test-artifact-1.0.0.jar");
        anotherTypeSolver = new CombinedTypeSolver(new JarTypeSolver(anotherPathToJar), new ReflectionTypeSolver());
    }

    ///
    /// Test misc
    ///

    @Test
    void testIsClass() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertTrue(compilationUnit.isClass());
    }

    @Test
    void testIsInterface() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertFalse(compilationUnit.isInterface());
    }

    @Test
    void testIsEnum() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertFalse(compilationUnit.isEnum());
    }

    @Test
    void testIsTypeVariable() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertFalse(compilationUnit.isTypeParameter());
    }

    @Test
    void testIsType() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertTrue(compilationUnit.isType());
    }

    @Test
    void testAsType() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asType());
    }

    @Test
    void testAsClass() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asClass());
    }

    @Test
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asInterface();
    });
}

    @Test
    void testAsEnum() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asEnum();
    });
}

    @Test
    void testGetPackageName() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast", compilationUnit.getPackageName());
    }

    @Test
    void testGetClassName() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("CompilationUnit", compilationUnit.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.CompilationUnit", compilationUnit.getQualifiedName());
    }

    @Test
    void testHasDirectlyAnnotation() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.TestClass");
        assertTrue(compilationUnit.hasDirectlyAnnotation("com.github.javaparser.test.TestAnnotation"));
    }

    @Test
    void testHasAnnotation() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.TestChildClass");
        assertTrue(compilationUnit.hasAnnotation("com.github.javaparser.test.TestAnnotation"));
    }

    @Test
    void testGetGenericTypeField(){
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) anotherTypeSolver.solveType("com.github.javaparser.test.ClassWithFields");
        List<ResolvedFieldDeclaration> declarationList = compilationUnit.getAllFields();
        assertEquals(6, declarationList.size());

        Map<String, ResolvedType> fields = new HashMap<>();
        for (ResolvedFieldDeclaration fieldDeclaration : declarationList) {
            String name = fieldDeclaration.getName();
            ResolvedType type = fieldDeclaration.getType();
            fields.put(name, type);
        }

        assertTrue(fields.containsKey("genericParamObjectField"));
        assertTrue(fields.containsKey("genericPrimitiveArrayField"));
        assertTrue(fields.containsKey("genericObjectArrayField"));
        assertTrue(fields.containsKey("genericField"));
        assertTrue(fields.containsKey("primitiveField"));
        assertTrue(fields.containsKey("objectField"));
    }

    @Test
    void testGetDeclaredMethods() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.Position");
        Set<ResolvedMethodDeclaration> methodsSet = compilationUnit.getDeclaredMethods();
        assertEquals(12, methodsSet.size());

        Map<String, MethodUsage> methods = new HashMap<>();
        for (ResolvedMethodDeclaration method : methodsSet) {
            methods.put(method.getName(), new MethodUsage(method));
        }

        assertTrue(methods.containsKey("pos"));
        assertEquals(2, methods.get("pos").getNoParams());
        assertTrue(methods.containsKey("withColumn"));
        assertEquals(1, methods.get("withColumn").getNoParams());
        assertTrue(methods.containsKey("withLine"));
        assertEquals(1, methods.get("withLine").getNoParams());
        assertTrue(methods.containsKey("valid"));
        assertEquals(0, methods.get("valid").getNoParams());
        assertTrue(methods.containsKey("invalid"));
        assertEquals(0, methods.get("invalid").getNoParams());
        assertTrue(methods.containsKey("orIfInvalid"));
        assertEquals(1, methods.get("orIfInvalid").getNoParams());
        assertTrue(methods.containsKey("isAfter"));
        assertEquals(1, methods.get("isAfter").getNoParams());
        assertTrue(methods.containsKey("isBefore"));
        assertEquals(1, methods.get("isBefore").getNoParams());
        assertTrue(methods.containsKey("compareTo"));
        assertEquals(1, methods.get("compareTo").getNoParams());
        assertTrue(methods.containsKey("equals"));
        assertEquals(1, methods.get("equals").getNoParams());
        assertTrue(methods.containsKey("hashCode"));
        assertEquals(0, methods.get("hashCode").getNoParams());
        assertTrue(methods.containsKey("toString"));
        assertEquals(0, methods.get("toString").getNoParams());
    }

    ///
    /// Test ancestors
    ///

    @Test
    void testGetSuperclass() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().orElseThrow(() -> new RuntimeException("super class unexpectedly empty")).getQualifiedName());
    }

    @Test
    void testGetSuperclassOfJavaLangObject() throws NotFoundException {
        CtClass javaLangObject = ClassPool.getDefault().get("java.lang.Object");
        JavassistClassDeclaration objectDeclaration = new JavassistClassDeclaration(javaLangObject, typeSolver);
        assertFalse(objectDeclaration.getSuperClass().isPresent());
    }

    @Test
    void testGetSuperclassWithoutTypeParameters() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().orElseThrow(() -> new RuntimeException("super class unexpectedly empty")).getQualifiedName());
    }

    @Test
    void testGetSuperclassWithTypeParameters() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", compilationUnit.getSuperClass().orElseThrow(() -> new RuntimeException("super class unexpectedly empty")).getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", compilationUnit.getSuperClass().orElseThrow(() -> new RuntimeException("super class unexpectedly empty")).typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetAllSuperclasses() {
        JavassistClassDeclaration cu = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllSuperClasses().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllAncestorsWithDepthFirstTraversalOrder() {
        JavassistClassDeclaration cu = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllAncestors().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));
    }

    @Test
    void testGetInterfaces() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));

        JavassistClassDeclaration coid = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.DocumentableNode"), coid.getInterfaces().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllInterfaces() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getAllInterfaces().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));

        JavassistClassDeclaration coid = (JavassistClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.NamedNode", "com.github.javaparser.ast.body.AnnotableNode", "com.github.javaparser.ast.DocumentableNode"), coid.getAllInterfaces().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllSuperclassesWithoutTypeParameters() {
        JavassistClassDeclaration cu = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllSuperClasses().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllSuperclassesWithTypeParameters() {
        JavassistClassDeclaration constructorDeclaration = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(3, constructorDeclaration.getAllSuperClasses().size());
        assertTrue(constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.body.BodyDeclaration")));
        assertTrue(constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.Node")));
        assertTrue(constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("java.lang.Object")));

        ResolvedReferenceType ancestor;

        ancestor = constructorDeclaration.getAllSuperClasses().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(2);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());
    }

    @Test
    void testGetInterfacesWithoutParameters() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));

        JavassistClassDeclaration coid = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.nodeTypes.NodeWithExtends", "com.github.javaparser.ast.nodeTypes.NodeWithImplements"), coid.getInterfaces().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));
    }

    @Test
    void testGetInterfacesWithParameters() {
        JavassistClassDeclaration constructorDeclaration = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(7, constructorDeclaration.getInterfaces().size());

        ResolvedReferenceType interfaze;

        interfaze = constructorDeclaration.getInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetAllInterfacesWithoutParameters() {
        JavassistClassDeclaration compilationUnit = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable"), compilationUnit.getAllInterfaces().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));

        JavassistClassDeclaration coid = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.nodeTypes.NodeWithExtends",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations",
                "java.lang.Cloneable",
                "com.github.javaparser.ast.nodeTypes.NodeWithImplements",
                "com.github.javaparser.ast.nodeTypes.NodeWithName",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers",
                "com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc",
                "com.github.javaparser.ast.nodeTypes.NodeWithMembers"), coid.getAllInterfaces().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllInterfacesWithParametersWithDepthFirstTraversalOrder() {
        JavassistClassDeclaration constructorDeclaration = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(9, constructorDeclaration.getAllInterfaces().size());

        ResolvedReferenceType interfaze;

        interfaze = constructorDeclaration.getAllInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(7);
        assertEquals("java.lang.Cloneable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetAncestorsWithTypeParametersWithDepthFirstTraversalOrder() {
        JavassistClassDeclaration constructorDeclaration = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(8, constructorDeclaration.getAncestors().size());

        ResolvedReferenceType ancestor;

        ancestor = constructorDeclaration.getAncestors().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetAllAncestorsWithoutTypeParametersWithDepthFirstTraversalOrder() {
        JavassistClassDeclaration cu = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllAncestors().stream().map(ResolvedReferenceType::getQualifiedName).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllAncestorsWithTypeParametersWithDepthFirstTraversalOrder() {
        JavassistClassDeclaration constructorDeclaration = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedReferenceType> ancestors = constructorDeclaration.getAllAncestors();

        assertEquals(12, ancestors.size());

        ResolvedReferenceType ancestor;

        ancestor = ancestors.get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = ancestors.get(2);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());

        ancestor = ancestors.get(3);
        assertEquals("java.lang.Cloneable", ancestor.getQualifiedName());

        ancestor = ancestors.get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = ancestors.get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(9);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(10);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(11);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());
    }

    @Nested
    class TestIsAssignableBy {
        @Test
        void whenNullTypeIsProvided() {
            JavassistClassDeclaration cu = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
            assertTrue(cu.isAssignableBy(NullType.INSTANCE));
        }

        @Test
        void whenLambdaArgumentTypePlaceholderIsProvided() {
            JavassistClassDeclaration cu = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
            assertFalse(cu.isAssignableBy(new LambdaArgumentTypePlaceholder(0)));
        }

        @Test
        void whenEqualTypeIsProvided() {
            JavassistClassDeclaration cu = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
            assertTrue(cu.isAssignableBy(cu));
        }

        @Test
        void whenSuperClassIsProvided() {
            ResolvedReferenceTypeDeclaration node = newTypeSolver.solveType("com.github.javaparser.ast.Node");
            JavassistClassDeclaration cu = (JavassistClassDeclaration) newTypeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
            assertTrue(cu.isAssignableBy(node));
        }

        @Test
        void whenInterfaceIsProvided() {
            JavassistInterfaceDeclaration nodeWithImplements = (JavassistInterfaceDeclaration) newTypeSolver.solveType(
                    "com.github.javaparser.ast.nodeTypes.NodeWithImplements");
            JavassistClassDeclaration classDeclaration = (JavassistClassDeclaration) newTypeSolver.solveType(
                    "com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
            assertTrue(classDeclaration.isAssignableBy(nodeWithImplements));
        }
    }

    @Override
    public AbstractClassDeclaration createValue() {
        try {
            TypeSolver typeSolver = new ReflectionTypeSolver();
            CtClass clazz = ClassPool.getDefault().getCtClass("java.lang.StringBuilder");
            return new JavassistClassDeclaration(clazz, typeSolver);
        } catch (NotFoundException e) {
            throw new RuntimeException("Unexpected error.", e);
        }
    }

    @Override
    public Optional<Node> getWrappedDeclaration(AssociableToAST associableToAST) {
        return Optional.empty();
    }

    @Override
    public boolean isFunctionalInterface(AbstractTypeDeclaration typeDeclaration) {
        return false;
    }

}
