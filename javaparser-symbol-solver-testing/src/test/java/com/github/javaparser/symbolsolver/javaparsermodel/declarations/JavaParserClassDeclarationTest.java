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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.symbolsolver.utils.LeanParserConfiguration;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.junit.jupiter.api.Assertions.*;

class JavaParserClassDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeSolver;
    private TypeSolver typeSolverNewCode;
    private ResolvedReferenceType string;
    private ResolvedReferenceType listOfBoolean;

    @BeforeEach
    void setup() {
        // clear internal caches
        JavaParserFacade.clearInstances();
        // init type solver...
        Path src = adaptPath("src/test/test_sourcecode/javaparser_src/proper_source");
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src, new LeanParserConfiguration()));
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath("src/test/test_sourcecode/javaparser_src/generated"), new LeanParserConfiguration()));
        typeSolver = combinedTypeSolver;

        Path srcNewCode = adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-core");
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new ReflectionTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(srcNewCode));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources")));
        typeSolverNewCode = combinedTypeSolverNewCode;

        TypeSolver ts = new ReflectionTypeSolver();
        string = new ReferenceTypeImpl(ts.solveType(String.class.getCanonicalName()));
        ResolvedReferenceType booleanC = new ReferenceTypeImpl(ts.solveType(Boolean.class.getCanonicalName()));
        listOfBoolean = new ReferenceTypeImpl(ts.solveType(List.class.getCanonicalName()), ImmutableList.of(booleanC));
        
        // init parser
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        // Setup parser
        StaticJavaParser.setConfiguration(configuration);
    }

    ///
    /// Test misc
    ///

    @Test
    void testIsClass() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertTrue(compilationUnit.isClass());
    }

    @Test
    void testIsInterface() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertFalse(compilationUnit.isInterface());
    }

    @Test
    void testIsEnum() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertFalse(compilationUnit.isEnum());
    }

    @Test
    void testIsTypeVariable() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertFalse(compilationUnit.isTypeParameter());
    }

    @Test
    void testIsType() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertTrue(compilationUnit.isType());
    }

    @Test
    void testAsType() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asType());
    }

    @Test
    void testAsClass() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asClass());
    }

    @Test
    void testAsInterface() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asInterface();
    });
}

    @Test
    void testAsEnum() {
        assertThrows(UnsupportedOperationException.class, () -> {
            JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asEnum();
    });
}

    @Test
    void testGetPackageName() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast", compilationUnit.getPackageName());
    }

    @Test
    void testGetClassName() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("CompilationUnit", compilationUnit.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.CompilationUnit", compilationUnit.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

    @Test
    void testGetSuperclassWithoutTypeParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().get().getQualifiedName());
    }

    @Test
    void testGetSuperclassWithTypeParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", compilationUnit.getSuperClass().get().getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", compilationUnit.getSuperClass().get().typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetAllSuperclassesWithoutTypeParameters() {
        JavaParserClassDeclaration cu = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllSuperclassesWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
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
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        JavaParserClassDeclaration coid = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.DocumentableNode"), coid.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetInterfacesWithParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
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
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable"), compilationUnit.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        JavaParserClassDeclaration coid = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.NamedNode", "com.github.javaparser.ast.body.AnnotableNode", "com.github.javaparser.ast.DocumentableNode"), coid.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllInterfacesWithParametersWithDepthFirstTraversalOrder() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
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
    void testGetAncestorsWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        
        List<ResolvedReferenceType> ancestors = constructorDeclaration.getAncestors();
        
        assertEquals(8, ancestors.size());

        ResolvedReferenceType ancestor;

        ancestor = ancestors.get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = ancestors.get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetAllAncestorsWithoutTypeParameters() {
        JavaParserClassDeclaration cu = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllAncestors().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllAncestorsWithDepthFirstTraversalOrder() {
        ResolvedReferenceTypeDeclaration integer = typeSolver.solveType(Integer.class.getCanonicalName());
        List<ResolvedReferenceType> ancestors = integer.getAllAncestors();
        assertEquals("java.lang.Number", ancestors.get(0).getQualifiedName());
        assertEquals("java.lang.Object", ancestors.get(1).getQualifiedName());
        assertEquals("java.io.Serializable", ancestors.get(2).getQualifiedName());
        assertEquals("java.lang.Comparable", ancestors.get(3).getQualifiedName());
    } 
        
    @Test
    void testGetAllAncestorsWithTypeParametersWithDepthFirstTraversalOrder() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        
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

        ancestor = constructorDeclaration.getAllAncestors().get(7);
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

    ///
    /// Test fields
    ///

    @Test
    void testGetFieldForExistingField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ResolvedFieldDeclaration fieldDeclaration;

        // declared field
        fieldDeclaration = constructorDeclaration.getField("modifiers");
        assertEquals("modifiers", fieldDeclaration.getName());
        assertEquals("java.util.EnumSet", fieldDeclaration.getType().asReferenceType().getQualifiedName());
        assertEquals(AccessSpecifier.PRIVATE, fieldDeclaration.accessSpecifier());
        assertFalse(fieldDeclaration.isStatic());

        // inherited field
        fieldDeclaration = constructorDeclaration.getField("annotations");
        assertEquals("annotations", fieldDeclaration.getName());
        assertEquals("java.util.List", fieldDeclaration.getType().asReferenceType().getQualifiedName());
        assertEquals(AccessSpecifier.PRIVATE, fieldDeclaration.accessSpecifier());
    }

    @Test
    void testGetFieldForUnexistingField() {
        assertThrows(UnsolvedSymbolException.class, () -> {
            JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        constructorDeclaration.getField("unexisting");
    });

}

    @Test
    void testGetAllFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedFieldDeclaration> allFields = constructorDeclaration.getAllFields();
        assertEquals(16, allFields.size());

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
        assertEquals("NODE_BY_BEGIN_POSITION", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(8);
        assertEquals("range", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(9);
        assertEquals("parentNode", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(10);
        assertEquals("childrenNodes", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(11);
        assertEquals("orphanComments", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(12);
        assertEquals("userData", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(13);
        assertEquals("comment", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(14);
        assertEquals("ABSOLUTE_BEGIN_LINE", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(15);
        assertEquals("ABSOLUTE_END_LINE", fieldDeclaration.getName());
    }

    @Test
    void testGetAllGenericFields() throws IOException {
        TypeSolver typeSolver = new ReflectionTypeSolver();

        CompilationUnit cu = parse(adaptPath("src/test/resources/GenericFields.java.txt"));
        JavaParserClassDeclaration classDeclaration = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CB"), typeSolver);

        assertEquals(3, classDeclaration.getAllFields().size());

        ReferenceTypeImpl rtClassDeclaration = new ReferenceTypeImpl(classDeclaration);

        assertEquals("s", classDeclaration.getAllFields().get(0).getName());
        assertEquals(string, classDeclaration.getAllFields().get(0).getType());
        assertEquals(string, rtClassDeclaration.getFieldType("s").get());

        assertEquals("t", classDeclaration.getAllFields().get(1).getName());
        assertEquals("java.util.List<java.lang.Boolean>", classDeclaration.getAllFields().get(1).getType().describe());
        assertEquals(listOfBoolean, rtClassDeclaration.getFieldType("t").get());

        assertEquals("i", classDeclaration.getAllFields().get(2).getName());
        assertEquals(ResolvedPrimitiveType.INT, classDeclaration.getAllFields().get(2).getType());
        assertEquals(ResolvedPrimitiveType.INT, rtClassDeclaration.getFieldType("i").get());
    }

    @Test
    void testGetAllStaticFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

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
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

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
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

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
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        Set<ResolvedMethodDeclaration> allMethods = constructorDeclaration.getDeclaredMethods();
        assertEquals(20, allMethods.size());

        List<ResolvedMethodDeclaration> sortedMethods = allMethods.stream()
                .sorted(Comparator.comparing(ResolvedMethodLikeDeclaration::getQualifiedSignature))
                .collect(Collectors.toList());

        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.accept(com.github.javaparser.ast.visitor.GenericVisitor<R, A>, A)", sortedMethods.get(0).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.accept(com.github.javaparser.ast.visitor.VoidVisitor<A>, A)", sortedMethods.get(1).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getBody()", sortedMethods.get(2).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString()", sortedMethods.get(3).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString(boolean, boolean)", sortedMethods.get(4).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getDeclarationAsString(boolean, boolean, boolean)", sortedMethods.get(5).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getJavaDoc()", sortedMethods.get(6).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getModifiers()", sortedMethods.get(7).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getName()", sortedMethods.get(8).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getNameExpr()", sortedMethods.get(9).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getParameters()", sortedMethods.get(10).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getThrows()", sortedMethods.get(11).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.getTypeParameters()", sortedMethods.get(12).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setBody(com.github.javaparser.ast.stmt.BlockStmt)", sortedMethods.get(13).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setModifiers(java.util.EnumSet<com.github.javaparser.ast.Modifier>)", sortedMethods.get(14).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setName(java.lang.String)", sortedMethods.get(15).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setNameExpr(com.github.javaparser.ast.expr.NameExpr)", sortedMethods.get(16).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setParameters(java.util.List<com.github.javaparser.ast.body.Parameter>)", sortedMethods.get(17).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setThrows(java.util.List<com.github.javaparser.ast.type.ReferenceType>)", sortedMethods.get(18).getQualifiedSignature());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration.setTypeParameters(java.util.List<com.github.javaparser.ast.type.TypeParameter>)", sortedMethods.get(19).getQualifiedSignature());
    }

    @Test
    void testGetAllMethods() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        Set<MethodUsage> allMethods = constructorDeclaration.getAllMethods();

        List<MethodUsage> sortedMethods = allMethods.stream()
                .sorted(Comparator.comparing(MethodUsage::getQualifiedSignature))
                .collect(Collectors.toList());

        List<String> signatures = sortedMethods.stream().map(m -> m.getQualifiedSignature()).collect(Collectors.toList());

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
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.addThrows(com.github.javaparser.ast.type.ReferenceType)",
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.addThrows(java.lang.Class<? extends java.lang.Throwable>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.Class<? extends java.lang.Throwable>)",
                "com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.String)",
                "java.lang.Object.finalize()",
                "java.lang.Object.getClass()",
                "java.lang.Object.notify()",
                "java.lang.Object.notifyAll()",
                "java.lang.Object.registerNatives()",
                "java.lang.Object.wait()",
                "java.lang.Object.wait(long)",
                "java.lang.Object.wait(long, int)"
        ));

        // Temporary workaround to allow tests to pass on JDK14
        if(TestJdk.getCurrentHostJdk().getMajorVersion() >= 14) {
            expected.remove("java.lang.Object.registerNatives()");
        }

        assertTrue(signatures.size() == expected.size());
        assertThat(signatures, containsInAnyOrder(expected.toArray()));
    }

    ///
    /// Test constructors
    ///

    @Test
    void testGetConstructors() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedConstructorDeclaration> constructors = constructorDeclaration.getConstructors();
        assertEquals(4, constructors.size());

        assertEquals("ConstructorDeclaration()", constructors.get(0).getSignature());
        assertEquals("ConstructorDeclaration(java.util.EnumSet<com.github.javaparser.ast.Modifier>, java.lang.String)", constructors.get(1).getSignature());
        assertEquals("ConstructorDeclaration(java.util.EnumSet<com.github.javaparser.ast.Modifier>, java.util.List<com.github.javaparser.ast.expr.AnnotationExpr>, java.util.List<com.github.javaparser.ast.type.TypeParameter>, java.lang.String, java.util.List<com.github.javaparser.ast.body.Parameter>, java.util.List<com.github.javaparser.ast.type.ReferenceType>, com.github.javaparser.ast.stmt.BlockStmt)", constructors.get(2).getSignature());
        assertEquals("ConstructorDeclaration(com.github.javaparser.Range, java.util.EnumSet<com.github.javaparser.ast.Modifier>, java.util.List<com.github.javaparser.ast.expr.AnnotationExpr>, java.util.List<com.github.javaparser.ast.type.TypeParameter>, java.lang.String, java.util.List<com.github.javaparser.ast.body.Parameter>, java.util.List<com.github.javaparser.ast.type.ReferenceType>, com.github.javaparser.ast.stmt.BlockStmt)", constructors.get(3).getSignature());
    }

    ///
    /// Resolution
    ///

    //SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes);
    @Test
    void testSolveMethodExisting() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<ResolvedMethodDeclaration> res;

        res = constructorDeclaration.solveMethod("isStatic", ImmutableList.of());
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.isStatic()", res.getCorrespondingDeclaration().getQualifiedSignature());

        res = constructorDeclaration.solveMethod("isThrows", ImmutableList.of(ReflectionFactory.typeUsageFor(RuntimeException.class.getClass(), typeSolverNewCode)));
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.Class<? extends java.lang.Throwable>)", res.getCorrespondingDeclaration().getQualifiedSignature());

        res = constructorDeclaration.solveMethod("isThrows", ImmutableList.of(ReflectionFactory.typeUsageFor(String.class, typeSolverNewCode)));
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.String)", res.getCorrespondingDeclaration().getQualifiedSignature());

        // This is solved because it is raw
        res = constructorDeclaration.solveMethod("isThrows", ImmutableList.of(ReflectionFactory.typeUsageFor(Class.class, typeSolverNewCode)));
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.isThrows(java.lang.Class<? extends java.lang.Throwable>)", res.getCorrespondingDeclaration().getQualifiedSignature());
    }

    @Test
    void testSolveMethodNotExisting() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<ResolvedMethodDeclaration> res;

        res = constructorDeclaration.solveMethod("unexistingMethod", ImmutableList.of());
        assertFalse(res.isSolved());

        res = constructorDeclaration.solveMethod("isStatic", ImmutableList.of(ResolvedPrimitiveType.BOOLEAN));
        assertFalse(res.isSolved());
    }

    @Test
    void testSolveMethodNotExistingBecauseOfTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<ResolvedMethodDeclaration> res;

        ResolvedReferenceType stringType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(String.class, typeSolverNewCode);
        ResolvedReferenceType rawClassType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(Class.class, typeSolverNewCode);
        ResolvedReferenceType classOfStringType = (ResolvedReferenceType) rawClassType.replaceTypeVariables(rawClassType.getTypeDeclaration().get().getTypeParameters().get(0), stringType);
        res = constructorDeclaration.solveMethod("isThrows", ImmutableList.of(classOfStringType));
        assertFalse(res.isSolved());
    }


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

    @Test
    void testHasDirectlyAnnotation() throws IOException {
        TypeSolver typeSolver = new ReflectionTypeSolver();

        CompilationUnit cu = parse(adaptPath("src/test/resources/Annotations.java.txt"));

        JavaParserClassDeclaration ca = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CA"), typeSolver);
        assertTrue(ca.hasDirectlyAnnotation("foo.bar.MyAnnotation"));
        assertFalse(ca.hasDirectlyAnnotation("foo.bar.MyAnnotation2"));
        assertFalse(ca.hasDirectlyAnnotation("MyAnnotation"));
        assertFalse(ca.hasDirectlyAnnotation("foo.bar.MyUnexistingAnnotation"));

        JavaParserClassDeclaration cb = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CB"), typeSolver);
        assertFalse(cb.hasDirectlyAnnotation("foo.bar.MyAnnotation"));
        assertTrue(cb.hasDirectlyAnnotation("foo.bar.MyAnnotation2"));
        assertFalse(cb.hasDirectlyAnnotation("MyAnnotation"));
        assertFalse(cb.hasDirectlyAnnotation("foo.bar.MyUnexistingAnnotation"));
    }

    // hasAnnotation

    @Test
    void testHasAnnotation() throws IOException {
        TypeSolver typeSolver = new ReflectionTypeSolver();

        CompilationUnit cu = parse(adaptPath("src/test/resources/Annotations.java.txt"));

        JavaParserClassDeclaration ca = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CA"), typeSolver);
        assertTrue(ca.hasAnnotation("foo.bar.MyAnnotation"));
        assertFalse(ca.hasAnnotation("foo.bar.MyAnnotation2"));
        assertFalse(ca.hasAnnotation("MyAnnotation"));
        assertFalse(ca.hasAnnotation("foo.bar.MyUnexistingAnnotation"));

        JavaParserClassDeclaration cb = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CB"), typeSolver);
        assertTrue(cb.hasAnnotation("foo.bar.MyAnnotation"));
        assertTrue(cb.hasAnnotation("foo.bar.MyAnnotation2"));
        assertFalse(cb.hasAnnotation("MyAnnotation"));
        assertFalse(cb.hasAnnotation("foo.bar.MyUnexistingAnnotation"));
    }

    ///
    ///
    ///

    // List<TypeParameterDeclaration> getTypeParameters();

    // AccessLevel accessLevel();

    ///
    /// Containment
    ///

    // Set<TypeDeclaration> internalTypes()

    // Optional<TypeDeclaration> containerType()


    @Test
    void testCanBeAssignedTo() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        ResolvedReferenceTypeDeclaration stringTypeDeclaration = typeSolver.solveType("java.lang.String");
        ResolvedReferenceTypeDeclaration objectTypeDeclaration = typeSolver.solveType("java.lang.Object");
        ResolvedReferenceTypeDeclaration cloneableTypeDeclaration = typeSolver.solveType("java.lang.Cloneable");
        ResolvedReferenceTypeDeclaration serializableTypeDeclaration = typeSolver.solveType("java.io.Serializable");

        // Assign "UP" (implicit) -- Assign to implicitly state ancestor (java.lang.Object) -- should be permitted
        assertTrue(compilationUnit.canBeAssignedTo(objectTypeDeclaration),"CompilationUnit should be reported as assignable to Object");

        // Assign "UP" (explicit) -- Assign to explicitly stated ancestors (extends/implements) -- should be permitted
        assertTrue(compilationUnit.canBeAssignedTo(cloneableTypeDeclaration),"CompilationUnit should be reported as assignable to Cloneable, because it extends Node which implements Cloneable");

        // Assign "SELF" -- Assign to self -- should be permitted
        assertTrue(compilationUnit.canBeAssignedTo(compilationUnit),"CompilationUnit should not be reported as assignable to CompilationUnit");
        assertTrue(stringTypeDeclaration.canBeAssignedTo(stringTypeDeclaration),"String should not be reported as assignable to String");
        assertTrue(objectTypeDeclaration.canBeAssignedTo(objectTypeDeclaration),"Object should be reported as assignable to Object");


        // Assign "DOWN" -- Assign ancestor to descendent -- should be rejected
        assertFalse(cloneableTypeDeclaration.canBeAssignedTo(compilationUnit),"CloneableTypeDeclaration should not be reported as assignable to CompilationUnit");
        assertFalse(objectTypeDeclaration.canBeAssignedTo(compilationUnit),"Object should not be reported as assignable to CompilationUnit");

        // Assign "independent" -- Assign to a class with a completely separate/independent hierarchy tree (up to Object, down to other) -- should be rejected
        assertFalse(compilationUnit.canBeAssignedTo(stringTypeDeclaration),"CompilationUnit should not be reported as assignable to String");

        // Assign "independent" -- Assign to a interface with a completely separate/independent hierarchy tree (up to Object, down to other) -- should be rejected
        assertFalse(compilationUnit.canBeAssignedTo(serializableTypeDeclaration), "CompilationUnit should not be reported as assignable to Serializable");
    }
    
    @Test
    // issue #3436 getAncestors()/getAllAncestors() does not work if base class starts with the same name
    public void getAncestors_with_child_name_is_part_of_ancestor_name() {
        List<ResolvedType> types = declaredTypes(
                "public class Foo extends FooBase {}",
                "public class FooBase {}");
        ResolvedType foo = types.get(0);
        List<ResolvedReferenceType> ancestors = foo.asReferenceType().getTypeDeclaration().get().getAncestors();
        assertTrue(ancestors.size() == 1);
        assertEquals("FooBase", ancestors.get(0).getQualifiedName());
    }
    
    private List<ResolvedType> declaredTypes(String... lines) {
        CompilationUnit tree = treeOf(lines);
        List<ResolvedType> results = Lists.newLinkedList();
        for (ClassOrInterfaceDeclaration classTree : tree.findAll(ClassOrInterfaceDeclaration.class)) {
            results.add(new ReferenceTypeImpl(classTree.resolve()));
        }
        return results;
    }

    private CompilationUnit treeOf(String... lines) {
        StringBuilder builder = new StringBuilder();
        for (String line : lines) {
            builder.append(line).append(System.lineSeparator());
        }
        return StaticJavaParser.parse(builder.toString());
    }

}
