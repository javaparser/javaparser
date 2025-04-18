/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.*;
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.core.resolution.MethodUsageResolutionCapabilityTest;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclaration;
import com.github.javaparser.symbolsolver.logic.AbstractTypeDeclarationTest;
import com.github.javaparser.symbolsolver.logic.MethodResolutionCapabilityTest;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

class JavaParserEnumDeclarationTest extends AbstractTypeDeclarationTest
        implements ResolvedEnumDeclarationTest, MethodResolutionCapabilityTest, MethodUsageResolutionCapabilityTest {

    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        Path srcNewCode = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        CombinedTypeSolver combinedtypeSolver = new CombinedTypeSolver();
        combinedtypeSolver.add(new ReflectionTypeSolver());
        combinedtypeSolver.add(new JavaParserTypeSolver(srcNewCode, new LeanParserConfiguration()));
        combinedtypeSolver.add(new JavaParserTypeSolver(
                adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"),
                new LeanParserConfiguration()));
        typeSolver = combinedtypeSolver;
    }

    ///
    /// Test misc
    ///

    @Test
    void testIsClass() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isClass());
    }

    @Test
    void testIsInterface() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isInterface());
    }

    @Test
    void testIsEnum() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isEnum());
    }

    @Test
    void testIsTypeVariable() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(false, modifier.isTypeParameter());
    }

    @Test
    void testIsType() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(true, modifier.isType());
    }

    @Test
    void testAsType() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asType());
    }

    @Test
    void testAsClass() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavaParserEnumDeclaration modifier =
                    (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
            modifier.asClass();
        });
    }

    @Test
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavaParserEnumDeclaration modifier =
                    (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
            modifier.asInterface();
        });
    }

    @Test
    void testAsEnum() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals(modifier, modifier.asEnum());
    }

    @Test
    void testGetPackageName() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast", modifier.getPackageName());
    }

    @Test
    void testGetClassName() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("Modifier", modifier.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        JavaParserEnumDeclaration modifier =
                (JavaParserEnumDeclaration) typeSolver.solveType("com.github.javaparser.ast.Modifier");
        assertEquals("com.github.javaparser.ast.Modifier", modifier.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

    @Test
    void getGetAncestors() {
        Path src = adaptPath("src/test/resources/enums");
        CombinedTypeSolver combinedtypeSolver = new CombinedTypeSolver();
        combinedtypeSolver.add(new ReflectionTypeSolver());
        combinedtypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));

        JavaParserEnumDeclaration enum1 = (JavaParserEnumDeclaration) combinedtypeSolver.solveType("EnumWithAncestor");
        List<ResolvedReferenceType> ancestors = enum1.getAncestors();
        assertEquals(2, ancestors.size());
        assertEquals("java.lang.Enum", ancestors.get(0).getQualifiedName());
        assertEquals("java.lang.Cloneable", ancestors.get(1).getQualifiedName());
    }

    //    @Test
    //    public void testGetSuperclassWithoutTypeParameters() {
    //        JavaParserEnumDeclaration modifier = (JavaParserEnumDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.Modifier");
    //        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().getQualifiedName());
    //    }

    @Test
    void testGetSuperclassWithTypeParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(
                "com.github.javaparser.ast.body.BodyDeclaration",
                compilationUnit.getSuperClass().get().getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                compilationUnit
                        .getSuperClass()
                        .get()
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());
    }

    @Test
    void testGetAllSuperclassesWithoutTypeParameters() {
        JavaParserClassDeclaration cu =
                (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(
                ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"),
                cu.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllSuperclassesWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(3, constructorDeclaration.getAllSuperClasses().size());

        ResolvedReferenceType ancestor;

        ancestor = constructorDeclaration.getAllSuperClasses().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(2);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());
    }

    //    @Test
    //    public void testGetInterfacesWithoutParameters() {
    //        JavaParserEnumDeclaration modifier = (JavaParserEnumDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.Modifier");
    //        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(i ->
    // i.getQualifiedName()).collect(Collectors.toSet()));
    //
    //        JavaParserClassDeclaration coid = (JavaParserClassDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
    //        assertEquals(ImmutableSet.of("com.github.javaparser.ast.DocumentableNode"),
    // coid.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    //    }

    @Test
    void testGetInterfacesWithParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(7, constructorDeclaration.getInterfaces().size());

        ResolvedReferenceType interfaze;

        interfaze = constructorDeclaration.getInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());
    }

    //    @Test
    //    public void testGetAllInterfacesWithoutParameters() {
    //        JavaParserEnumDeclaration modifier = (JavaParserEnumDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.Modifier");
    //        assertEquals(ImmutableSet.of("java.lang.Cloneable"), compilationUnit.getAllInterfaces().stream().map(i ->
    // i.getQualifiedName()).collect(Collectors.toSet()));
    //
    //        JavaParserClassDeclaration coid = (JavaParserClassDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
    //        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.NamedNode",
    // "com.github.javaparser.ast.body.AnnotableNode", "com.github.javaparser.ast.DocumentableNode"),
    // coid.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    //    }

    @Test
    void testGetAllInterfacesWithParametersWithDepthFirstTraversalOrder() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(9, constructorDeclaration.getAllInterfaces().size());

        ResolvedReferenceType interfaze;

        interfaze = constructorDeclaration.getAllInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(7);
        assertEquals("java.lang.Cloneable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", interfaze.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                interfaze
                        .typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());
    }

    @Test
    void testGetAncestorsWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(8, constructorDeclaration.getAncestors().size());

        ResolvedReferenceType ancestor;

        ancestor = constructorDeclaration.getAncestors().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());
    }

    @Test
    void testGetAllAncestorsWithoutTypeParametersWithDepthFirstTraversalOrder() {
        JavaParserClassDeclaration cu =
                (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(
                ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.Node", "java.lang.Object"),
                cu.getAllAncestors().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllAncestorsWithTypeParametersWithDepthFirstTraversalOrder() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedReferenceType> ancestors = constructorDeclaration.getAllAncestors();

        assertEquals(12, ancestors.size());

        ResolvedReferenceType ancestor;

        ancestor = ancestors.get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = ancestors.get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(2);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());

        ancestor = ancestors.get(3);
        assertEquals("java.lang.Cloneable", ancestor.getQualifiedName());

        ancestor = ancestors.get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = ancestors.get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = ancestors.get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = ancestors.get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = ancestors.get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = ancestors.get(9);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = ancestors.get(10);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());

        ancestor = ancestors.get(11);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration",
                ancestor.typeParametersMap()
                        .getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T")
                        .get()
                        .asReferenceType()
                        .getQualifiedName());
    }

    ///
    /// Test fields
    ///

    @Test
    void testGetFieldForExistingField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ResolvedFieldDeclaration fieldDeclaration;

        // declared field
        fieldDeclaration = constructorDeclaration.getField("modifiers");
        assertEquals("modifiers", fieldDeclaration.getName());
        assertEquals(
                "java.util.EnumSet",
                fieldDeclaration.getType().asReferenceType().getQualifiedName());
        assertEquals(AccessSpecifier.PRIVATE, fieldDeclaration.accessSpecifier());
        assertFalse(fieldDeclaration.isStatic());

        // inherited field
        fieldDeclaration = constructorDeclaration.getField("annotations");
        assertEquals("annotations", fieldDeclaration.getName());
        assertEquals(
                "java.util.List", fieldDeclaration.getType().asReferenceType().getQualifiedName());
        assertEquals(AccessSpecifier.PRIVATE, fieldDeclaration.accessSpecifier());
    }

    @Test
    void testGetFieldForUnexistingField() {
        assertThrows(UnsolvedSymbolException.class, () -> {
            JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                    typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
            constructorDeclaration.getField("unexisting");
        });
    }

    @Test
    void testGetAllFields() {
        Path src = adaptPath("src/test/resources/enums");
        CombinedTypeSolver combinedtypeSolver = new CombinedTypeSolver();
        combinedtypeSolver.add(new ReflectionTypeSolver());
        combinedtypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));

        JavaParserEnumDeclaration enumDecl = (JavaParserEnumDeclaration) combinedtypeSolver.solveType("COLOR");
        assertEquals(2, enumDecl.getAllFields().size());
        assertEquals("int", enumDecl.getAllFields().get(0).getType().describe());
        assertEquals("int", enumDecl.getAllFields().get(1).getType().describe());
    }

    @Test
    void testGetAllStaticFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedFieldDeclaration> allFields = constructorDeclaration.getAllStaticFields();
        assertEquals(3, allFields.size());

        ResolvedFieldDeclaration fieldDeclaration;

        fieldDeclaration = allFields.get(0);
        assertEquals("NODE_BY_BEGIN_POSITION", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(1);
        assertEquals("ABSOLUTE_BEGIN_LINE", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(2);
        assertEquals("ABSOLUTE_END_LINE", fieldDeclaration.getName());
    }

    @Test
    void testGetAllNonStaticFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedFieldDeclaration> allFields = constructorDeclaration.getAllNonStaticFields();
        assertEquals(13, allFields.size());

        ResolvedFieldDeclaration fieldDeclaration;

        fieldDeclaration = allFields.get(0);
        assertEquals("modifiers", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(1);
        assertEquals("typeParameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(2);
        assertEquals("name", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(3);
        assertEquals("parameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(4);
        assertEquals("throws_", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(5);
        assertEquals("body", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(6);
        assertEquals("annotations", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(7);
        assertEquals("range", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(8);
        assertEquals("parentNode", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(9);
        assertEquals("childrenNodes", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(10);
        assertEquals("orphanComments", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(11);
        assertEquals("userData", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(12);
        assertEquals("comment", fieldDeclaration.getName());
    }

    @Test
    void testGetDeclaredFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedFieldDeclaration> allFields = constructorDeclaration.getDeclaredFields();
        assertEquals(6, allFields.size());

        ResolvedFieldDeclaration fieldDeclaration;

        fieldDeclaration = allFields.get(0);
        assertEquals("modifiers", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(1);
        assertEquals("typeParameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(2);
        assertEquals("name", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(3);
        assertEquals("parameters", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(4);
        assertEquals("throws_", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(5);
        assertEquals("body", fieldDeclaration.getName());
    }

    ///
    /// Test methods
    ///

    @Test
    void testGetDeclaredMethods() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        Set<ResolvedMethodDeclaration> allMethods = constructorDeclaration.getDeclaredMethods();
        assertEquals(20, allMethods.size());

        List<ResolvedMethodDeclaration> sortedMethods = allMethods.stream()
                .sorted(Comparator.comparing(ResolvedMethodLikeDeclaration::getQualifiedSignature))
                .collect(Collectors.toList());

        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.accept(com.github.javaparser.ast.visitor.GenericVisitor<R, A>, A)",
                sortedMethods.get(0).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.accept(com.github.javaparser.ast.visitor.VoidVisitor<A>, A)",
                sortedMethods.get(1).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getBody()",
                sortedMethods.get(2).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString()",
                sortedMethods.get(3).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString(boolean, boolean)",
                sortedMethods.get(4).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString(boolean, boolean, boolean)",
                sortedMethods.get(5).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getJavaDoc()",
                sortedMethods.get(6).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getModifiers()",
                sortedMethods.get(7).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getName()",
                sortedMethods.get(8).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getNameExpr()",
                sortedMethods.get(9).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getParameters()",
                sortedMethods.get(10).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getThrows()",
                sortedMethods.get(11).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.getTypeParameters()",
                sortedMethods.get(12).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.setBody(com.github.javaparser.ast.stmt.BlockStmt)",
                sortedMethods.get(13).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.setModifiers(java.util.EnumSet<com.github.javaparser.ast.Modifier>)",
                sortedMethods.get(14).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.setName(java.lang.String)",
                sortedMethods.get(15).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.setNameExpr(com.github.javaparser.ast.expr.NameExpr)",
                sortedMethods.get(16).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.setParameters(java.util.List<com.github.javaparser.ast.body.Parameter>)",
                sortedMethods.get(17).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.setThrows(java.util.List<com.github.javaparser.ast.type.ReferenceType>)",
                sortedMethods.get(18).getQualifiedSignature());
        assertEquals(
                "com.github.javaparser.ast.body.ConstructorDeclaration.setTypeParameters(java.util.List<com.github.javaparser.ast.type.TypeParameter>)",
                sortedMethods.get(19).getQualifiedSignature());
    }

    @Test
    void testGetAllMethods() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        Set<MethodUsage> allMethods = constructorDeclaration.getAllMethods();

        List<MethodUsage> sortedMethods = allMethods.stream()
                .sorted(Comparator.comparing(MethodUsage::getQualifiedSignature))
                .collect(Collectors.toList());

        List<String> signatures =
                sortedMethods.stream().map(m -> m.getQualifiedSignature()).collect(Collectors.toList());

        signatures.stream().forEach(m -> System.out.println(m));

        List<String> expected = new ArrayList<>(Arrays.asList(
                "com.github.javaparser.ast.Node.addOrphanComment(com.github.javaparser.ast.comments.Comment)",
                "com.github.javaparser.ast.Node.clone()",
                "com.github.javaparser.ast.Node.contains(com.github.javaparser.ast.Node)",
                "com.github.javaparser.ast.Node.equals(java.lang.Object)",
                "com.github.javaparser.ast.Node.getAllContainedComments()",
                "com.github.javaparser.ast.Node.getBegin()",
                "com.github.javaparser.ast.Node.getChildrenNodes()",
                "com.github.javaparser.ast.Node.getComment()",
                "com.github.javaparser.ast.Node.getEnd()",
                "com.github.javaparser.ast.Node.getNodesByType(java.lang.Class<N>)",
                "com.github.javaparser.ast.Node.getOrphanComments()",
                "com.github.javaparser.ast.Node.getParentNode()",
                "com.github.javaparser.ast.Node.getParentNodeOfType(java.lang.Class<T>)",
                "com.github.javaparser.ast.Node.getRange()",
                "com.github.javaparser.ast.Node.getUserData(com.github.javaparser.ast.UserDataKey<M>)",
                "com.github.javaparser.ast.Node.hasComment()",
                "com.github.javaparser.ast.Node.hashCode()",
                "com.github.javaparser.ast.Node.isPositionedAfter(com.github.javaparser.Position)",
                "com.github.javaparser.ast.Node.isPositionedBefore(com.github.javaparser.Position)",
                "com.github.javaparser.ast.Node.setAsParentNodeOf(com.github.javaparser.ast.Node)",
                "com.github.javaparser.ast.Node.setAsParentNodeOf(java.util.List<? extends com.github.javaparser.ast.Node>)",
                "com.github.javaparser.ast.Node.setBegin(com.github.javaparser.Position)",
                "com.github.javaparser.ast.Node.setBlockComment(java.lang.String)",
                "com.github.javaparser.ast.Node.setComment(com.github.javaparser.ast.comments.Comment)",
                "com.github.javaparser.ast.Node.setEnd(com.github.javaparser.Position)",
                "com.github.javaparser.ast.Node.setLineComment(java.lang.String)",
                "com.github.javaparser.ast.Node.setParentNode(com.github.javaparser.ast.Node)",
                "com.github.javaparser.ast.Node.setRange(com.github.javaparser.Range)",
                "com.github.javaparser.ast.Node.setUserData(com.github.javaparser.ast.UserDataKey<M>, M)",
                "com.github.javaparser.ast.Node.toString()",
                "com.github.javaparser.ast.Node.toStringWithoutComments()",
                "com.github.javaparser.ast.Node.tryAddImportToParentCompilationUnit(java.lang.Class<?>)",
                "com.github.javaparser.ast.body.BodyDeclaration.getAnnotations()",
                "com.github.javaparser.ast.body.BodyDeclaration.setAnnotations(java.util.List<com.github.javaparser.ast.expr.AnnotationExpr>)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.accept(com.github.javaparser.ast.visitor.GenericVisitor<R, A>, A)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.accept(com.github.javaparser.ast.visitor.VoidVisitor<A>, A)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getBody()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString(boolean, boolean)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString(boolean, boolean, boolean)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getJavaDoc()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getModifiers()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getName()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getNameExpr()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getParameters()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getThrows()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.getTypeParameters()",
                "com.github.javaparser.ast.body.ConstructorDeclaration.setBody(com.github.javaparser.ast.stmt.BlockStmt)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.setModifiers(java.util.EnumSet<com.github.javaparser.ast.Modifier>)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.setName(java.lang.String)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.setNameExpr(com.github.javaparser.ast.expr.NameExpr)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.setParameters(java.util.List<com.github.javaparser.ast.body.Parameter>)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.setThrows(java.util.List<com.github.javaparser.ast.type.ReferenceType>)",
                "com.github.javaparser.ast.body.ConstructorDeclaration.setTypeParameters(java.util.List<com.github.javaparser.ast.type.TypeParameter>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.addAnnotation(java.lang.Class<? extends java.lang.annotation.Annotation>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.addAnnotation(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.addMarkerAnnotation(java.lang.Class<? extends java.lang.annotation.Annotation>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.addMarkerAnnotation(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.addSingleMemberAnnotation(java.lang.Class<? extends java.lang.annotation.Annotation>, java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.addSingleMemberAnnotation(java.lang.String, java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.getAnnotationByClass(java.lang.Class<? extends java.lang.annotation.Annotation>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.getAnnotationByName(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.isAnnotationPresent(java.lang.Class<? extends java.lang.annotation.Annotation>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.isAnnotationPresent(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.createBody()",
                "com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.setBody(com.github.javaparser.ast.stmt.BlockStmt)",
                "com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.setJavaDocComment(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.addModifier(com.github.javaparser.ast.Modifier...)",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isAbstract()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isFinal()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isNative()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isPrivate()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isProtected()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isPublic()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isStatic()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isStrictfp()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isSynchronized()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isTransient()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isVolatile()",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.setModifiers(java.util.EnumSet<com.github.javaparser.ast.Modifier>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithName.setName(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.addAndGetParameter(com.github.javaparser.ast.body.Parameter)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.addAndGetParameter(com.github.javaparser.ast.type.Type, java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.addAndGetParameter(java.lang.Class<?>, java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.addAndGetParameter(java.lang.String, java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.addParameter(com.github.javaparser.ast.body.Parameter)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.addParameter(com.github.javaparser.ast.type.Type, java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.addParameter(java.lang.Class<?>, java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.addParameter(java.lang.String, java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.getParamByName(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.getParamByType(java.lang.Class<?>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.getParamByType(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithParameters.setParameters(java.util.List<com.github.javaparser.ast.body.Parameter>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.addThrows(com.github.javaparser.ast.type.ReferenceType)",
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.addThrows(java.lang.Class<? extends java.lang.Throwable>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.Class<? extends java.lang.Throwable>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.String)",
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.setThrows(java.util.List<com.github.javaparser.ast.type.ReferenceType>)",
                "java.lang.Object.clone()",
                "java.lang.Object.finalize()",
                "java.lang.Object.getClass()",
                "java.lang.Object.notify()",
                "java.lang.Object.notifyAll()",
                "java.lang.Object.registerNatives()",
                "java.lang.Object.wait()",
                "java.lang.Object.wait(long)",
                "java.lang.Object.wait(long, int)"));

        // Temporary workaround to allow tests to pass on JDK14
        if (TestJdk.getCurrentHostJdk().getMajorVersion() >= 14) {
            expected.remove("java.lang.Object.registerNatives()");
        }

        assertThat(signatures, containsInAnyOrder(expected.toArray()));
    }

    ///
    /// Test constructors
    ///

    @Test
    void testGetConstructors() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedConstructorDeclaration> constructors = constructorDeclaration.getConstructors();
        assertEquals(4, constructors.size());

        assertEquals("ConstructorDeclaration()", constructors.get(0).getSignature());
        assertEquals(
                "ConstructorDeclaration(java.util.EnumSet<com.github.javaparser.ast.Modifier>, java.lang.String)",
                constructors.get(1).getSignature());
        assertEquals(
                "ConstructorDeclaration(java.util.EnumSet<com.github.javaparser.ast.Modifier>, java.util.List<com.github.javaparser.ast.expr.AnnotationExpr>, java.util.List<com.github.javaparser.ast.type.TypeParameter>, java.lang.String, java.util.List<com.github.javaparser.ast.body.Parameter>, java.util.List<com.github.javaparser.ast.type.ReferenceType>, com.github.javaparser.ast.stmt.BlockStmt)",
                constructors.get(2).getSignature());
        assertEquals(
                "ConstructorDeclaration(com.github.javaparser.Range, java.util.EnumSet<com.github.javaparser.ast.Modifier>, java.util.List<com.github.javaparser.ast.expr.AnnotationExpr>, java.util.List<com.github.javaparser.ast.type.TypeParameter>, java.lang.String, java.util.List<com.github.javaparser.ast.body.Parameter>, java.util.List<com.github.javaparser.ast.type.ReferenceType>, com.github.javaparser.ast.stmt.BlockStmt)",
                constructors.get(3).getSignature());
    }

    ///
    /// Resolution
    ///

    // SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes);
    @Test
    void testSolveMethodExisting() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<ResolvedMethodDeclaration> res;

        res = constructorDeclaration.solveMethod("isStatic", ImmutableList.of());
        assertEquals(
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isStatic()",
                res.getCorrespondingDeclaration().getQualifiedSignature());

        res = constructorDeclaration.solveMethod(
                "isThrows",
                ImmutableList.of(ReflectionFactory.typeUsageFor(RuntimeException.class.getClass(), typeSolver)));
        assertEquals(
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.Class<? extends java.lang.Throwable>)",
                res.getCorrespondingDeclaration().getQualifiedSignature());

        res = constructorDeclaration.solveMethod(
                "isThrows", ImmutableList.of(ReflectionFactory.typeUsageFor(String.class, typeSolver)));
        assertEquals(
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.String)",
                res.getCorrespondingDeclaration().getQualifiedSignature());

        // This is solved because it is raw
        res = constructorDeclaration.solveMethod(
                "isThrows", ImmutableList.of(ReflectionFactory.typeUsageFor(Class.class, typeSolver)));
        assertEquals(
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.Class<? extends java.lang.Throwable>)",
                res.getCorrespondingDeclaration().getQualifiedSignature());
    }

    @Test
    void testSolveMethodNotExisting() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
                typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<ResolvedMethodDeclaration> res;

        res = constructorDeclaration.solveMethod("unexistingMethod", ImmutableList.of());
        assertEquals(false, res.isSolved());

        res = constructorDeclaration.solveMethod("isStatic", ImmutableList.of(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(false, res.isSolved());
    }

    //    @Test
    //    public void testSolveMethodNotExistingBecauseOfTypeParameters() {
    //        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
    //
    //        SymbolReference<ResolvedMethodDeclaration> res = null;
    //
    //        ResolvedReferenceType stringType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(String.class,
    // typeSolver);
    //        ResolvedReferenceType rawClassType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(Class.class,
    // typeSolver);
    //        ResolvedReferenceType classOfStringType = (ResolvedReferenceType) rawClassType.replaceTypeVariables("T",
    // stringType);
    //        res = constructorDeclaration.solveMethod("isThrows", ImmutableList.of(classOfStringType));
    //        assertEquals(false, res.isSolved());
    //    }

    //    @Test
    //    public void testSolveSymbolUnexisting() {
    //        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
    //
    //        SymbolReference<? extends ResolvedValueDeclaration> res = constructorDeclaration.solveSymbol("unexisting",
    // typeSolver);
    //        assertEquals(false, res.isSolved());
    //    }
    //
    //    @Test
    //    public void testSolveSymbolToDeclaredField() {
    //        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
    //
    //        SymbolReference<? extends ResolvedValueDeclaration> res = constructorDeclaration.solveSymbol("name",
    // typeSolver);
    //        assertEquals(true, res.isSolved());
    //        assertEquals(true, res.getCorrespondingDeclaration().isField());
    //    }
    //
    //    @Test
    //    public void testSolveSymbolToInheritedPublicField() {
    //        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
    //
    //        SymbolReference<? extends ResolvedValueDeclaration> res =
    // constructorDeclaration.solveSymbol("NODE_BY_BEGIN_POSITION", typeSolver);
    //        assertEquals(true, res.isSolved());
    //        assertEquals(true, res.getCorrespondingDeclaration().isField());
    //    }
    //
    //    @Test
    //    public void testSolveSymbolToInheritedPrivateField() {
    //        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration)
    // typeSolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
    //
    //        SymbolReference<? extends ResolvedValueDeclaration> res = constructorDeclaration.solveSymbol("parentNode",
    // typeSolver);
    //        assertEquals(false, res.isSolved());
    //    }

    ///
    /// Assignability
    ///

    // boolean isAssignableBy(Type type);

    // boolean canBeAssignedTo(TypeDeclaration other)

    // boolean isAssignableBy(TypeDeclaration other);

    ///
    /// Annotations
    ///

    // hasDirectlyAnnotation

    // hasAnnotation

    ///
    ///
    ///

    // List<TypeParameterDeclaration> getTypeParameters();

    // AccessLevel accessLevel();

    ///
    /// Containment
    ///

    // Set<TypeDeclaration> internalTypes()
    @Test
    void testGetInternalTypes() {
        Path src = adaptPath("src/test/resources/enums");
        CombinedTypeSolver combinedtypeSolver = new CombinedTypeSolver();
        combinedtypeSolver.add(new ReflectionTypeSolver());
        combinedtypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));

        JavaParserEnumDeclaration enum1 = (JavaParserEnumDeclaration) combinedtypeSolver.solveType("EnumWithAncestor");
        Set<ResolvedReferenceTypeDeclaration> internalTypes1 = enum1.internalTypes();
        assertEquals(0, internalTypes1.size());

        JavaParserEnumDeclaration enum2 = (JavaParserEnumDeclaration) combinedtypeSolver.solveType("EnumWithInnerType");
        Set<ResolvedReferenceTypeDeclaration> internalTypes2 = enum2.internalTypes();
        assertEquals(1, internalTypes2.size());
        assertEquals(
                "EnumWithInnerType.EnumInner", internalTypes2.iterator().next().getQualifiedName());
    }

    // Optional<TypeDeclaration> containerType()

    ///
    /// Annotations
    ///

    // Issue 1749
    @Test
    void testHasDirectlyAnnotationNegative() {
        ParserConfiguration parserConfiguration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = new JavaParser(parserConfiguration)
                .parse(
                        ParseStart.COMPILATION_UNIT,
                        new StringProvider("public class Employee {"
                                + "    public enum Weekend { SUNDAY, SATURDAY }"
                                + "    private Weekend weekend;"
                                + "}"))
                .getResult()
                .get();
        FieldDeclaration field =
                cu.getClassByName("Employee").get().getMembers().get(1).asFieldDeclaration();
        ResolvedReferenceTypeDeclaration dec = field.getElementType()
                .resolve()
                .asReferenceType()
                .getTypeDeclaration()
                .get();
        assertEquals(false, dec.hasDirectlyAnnotation("javax.persistence.Embeddable"));
    }

    // Issue 1749
    @Test
    void testHasDirectlyAnnotationPositive() {
        ParserConfiguration parserConfiguration =
                new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = new JavaParser(parserConfiguration)
                .parse(
                        ParseStart.COMPILATION_UNIT,
                        new StringProvider("@interface MyAnno {} public class Employee {"
                                + "    public @MyAnno enum Weekend { SUNDAY, SATURDAY }"
                                + "    private Weekend weekend;"
                                + "}"))
                .getResult()
                .get();
        FieldDeclaration field =
                cu.getClassByName("Employee").get().getMembers().get(1).asFieldDeclaration();
        ResolvedReferenceTypeDeclaration dec = field.getElementType()
                .resolve()
                .asReferenceType()
                .getTypeDeclaration()
                .get();
        assertEquals(false, dec.hasDirectlyAnnotation("javax.persistence.Embeddable"));
        assertEquals(true, dec.hasDirectlyAnnotation("MyAnno"));
    }

    @Override
    public Optional<Node> getWrappedDeclaration(AssociableToAST associableToAST) {
        return Optional.of(
                safeCast(associableToAST, JavaParserEnumDeclaration.class).getWrappedNode());
    }

    @Override
    public JavaParserEnumDeclaration createValue() {
        EnumDeclaration enumDeclaration = StaticJavaParser.parse("enum A {}")
                .findFirst(EnumDeclaration.class)
                .get();
        TypeSolver typeSolver = new ReflectionTypeSolver();
        return new JavaParserEnumDeclaration(enumDeclaration, typeSolver);
    }

    @Override
    public boolean isFunctionalInterface(AbstractTypeDeclaration typeDeclaration) {
        return false;
    }

    @Disabled(
            value = "This test was disable in this class due to a bug reported at https://github"
                    + ".com/javaparser/javaparser/issues/3061. It should be renabled when the issue is fixed.")
    @Test
    @Override
    public void containerTypeCantBeNull() {
        super.containerTypeCantBeNull();
    }
}
