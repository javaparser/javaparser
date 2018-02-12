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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseException;
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.resolution.MethodUsage;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.symbolsolver.AbstractTest;
import com.github.javaparser.symbolsolver.javaparser.Navigator;
import com.github.javaparser.symbolsolver.model.resolution.SymbolReference;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionFactory;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

public class JavaParserClassDeclarationTest extends AbstractTest {

    private TypeSolver typeSolver;
    private TypeSolver typeSolverNewCode;
    private ResolvedReferenceType string;
    private ResolvedReferenceType listOfBoolean;

    @Before
    public void setup() {
        File src = adaptPath(new File("src/test/test_sourcecode/javaparser_src/proper_source"));
        CombinedTypeSolver combinedTypeSolver = new CombinedTypeSolver();
        combinedTypeSolver.add(new ReflectionTypeSolver());
        combinedTypeSolver.add(new JavaParserTypeSolver(src));
        combinedTypeSolver.add(new JavaParserTypeSolver(adaptPath(new File("src/test/test_sourcecode/javaparser_src/generated"))));
        typeSolver = combinedTypeSolver;

        File srcNewCode = adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-core"));
        CombinedTypeSolver combinedTypeSolverNewCode = new CombinedTypeSolver();
        combinedTypeSolverNewCode.add(new ReflectionTypeSolver());
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(srcNewCode));
        combinedTypeSolverNewCode.add(new JavaParserTypeSolver(adaptPath(new File("src/test/test_sourcecode/javaparser_new_src/javaparser-generated-sources"))));
        typeSolverNewCode = combinedTypeSolverNewCode;

        TypeSolver ts = new ReflectionTypeSolver();
        string = new ReferenceTypeImpl(ts.solveType(String.class.getCanonicalName()), ts);
        ResolvedReferenceType booleanC = new ReferenceTypeImpl(ts.solveType(Boolean.class.getCanonicalName()), ts);
        listOfBoolean = new ReferenceTypeImpl(ts.solveType(List.class.getCanonicalName()), ImmutableList.of(booleanC), ts);
    }

    ///
    /// Test misc
    ///

    @Test
    public void testIsClass() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(true, compilationUnit.isClass());
    }

    @Test
    public void testIsInterface() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isInterface());
    }

    @Test
    public void testIsEnum() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isEnum());
    }

    @Test
    public void testIsTypeVariable() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(false, compilationUnit.isTypeParameter());
    }

    @Test
    public void testIsType() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(true, compilationUnit.isType());
    }

    @Test
    public void testAsType() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asType());
    }

    @Test
    public void testAsClass() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(compilationUnit, compilationUnit.asClass());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsInterface() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asInterface();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsEnum() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        compilationUnit.asEnum();
    }

    @Test
    public void testGetPackageName() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast", compilationUnit.getPackageName());
    }

    @Test
    public void testGetClassName() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("CompilationUnit", compilationUnit.getClassName());
    }

    @Test
    public void testGetQualifiedName() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.CompilationUnit", compilationUnit.getQualifiedName());
    }

    ///
    /// Test ancestors
    ///

    @Test
    public void testGetSuperclassWithoutTypeParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().getQualifiedName());
    }

    @Test
    public void testGetSuperclassWithTypeParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", compilationUnit.getSuperClass().getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", compilationUnit.getSuperClass().typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAllSuperclassesWithoutTypeParameters() {
        JavaParserClassDeclaration cu = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllSuperclassesWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(3, constructorDeclaration.getAllSuperClasses().size());
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.body.BodyDeclaration")));
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.Node")));
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("java.lang.Object")));

        ResolvedReferenceType ancestor = null;

        ancestor = constructorDeclaration.getAllSuperClasses().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(2);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());
    }

    @Test
    public void testGetInterfacesWithoutParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        JavaParserClassDeclaration coid = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.DocumentableNode"), coid.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetInterfacesWithParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(7, constructorDeclaration.getInterfaces().size());

        ResolvedReferenceType interfaze = null;

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
    public void testGetAllInterfacesWithoutParameters() {
        JavaParserClassDeclaration compilationUnit = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable"), compilationUnit.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        JavaParserClassDeclaration coid = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.NamedNode", "com.github.javaparser.ast.body.AnnotableNode", "com.github.javaparser.ast.DocumentableNode"), coid.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllInterfacesWithParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(9, constructorDeclaration.getAllInterfaces().size());

        ResolvedReferenceType interfaze = null;

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
    public void testGetAncestorsWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(8, constructorDeclaration.getAncestors().size());

        ResolvedReferenceType ancestor = null;

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
    public void testGetAllAncestorsWithoutTypeParameters() {
        JavaParserClassDeclaration cu = (JavaParserClassDeclaration) typeSolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllAncestors().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllAncestorsWithTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(12, constructorDeclaration.getAllAncestors().size());

        ResolvedReferenceType ancestor = null;

        ancestor = constructorDeclaration.getAllAncestors().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(2);
        assertEquals("java.lang.Cloneable", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(4);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithName.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(9);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(10);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(11);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.T").get().asReferenceType().getQualifiedName());
    }

    ///
    /// Test fields
    ///

    @Test
    public void testGetFieldForExistingField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ResolvedFieldDeclaration fieldDeclaration = null;

        // declared field
        fieldDeclaration = constructorDeclaration.getField("modifiers");
        assertEquals("modifiers", fieldDeclaration.getName());
        assertEquals("java.util.EnumSet", fieldDeclaration.getType().asReferenceType().getQualifiedName());
        assertEquals(AccessSpecifier.PRIVATE, fieldDeclaration.accessSpecifier());
        assertEquals(false, fieldDeclaration.isStatic());

        // inherited field
        fieldDeclaration = constructorDeclaration.getField("annotations");
        assertEquals("annotations", fieldDeclaration.getName());
        assertEquals("java.util.List", fieldDeclaration.getType().asReferenceType().getQualifiedName());
        assertEquals(AccessSpecifier.PRIVATE, fieldDeclaration.accessSpecifier());
    }

    @Test(expected = UnsolvedSymbolException.class)
    public void testGetFieldForUnexistingField() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        constructorDeclaration.getField("unexisting");
    }

    @Test
    public void testGetAllFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedFieldDeclaration> allFields = constructorDeclaration.getAllFields();
        assertEquals(16, allFields.size());

        ResolvedFieldDeclaration fieldDeclaration = null;

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
    public void testGetAllGenericFields() throws IOException, ParseException {
        TypeSolver typeSolver = new ReflectionTypeSolver();

        CompilationUnit cu = JavaParser.parse(adaptPath(new File("src/test/resources/GenericFields.java.txt")));
        JavaParserClassDeclaration classDeclaration = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CB"), typeSolver);

        assertEquals(3, classDeclaration.getAllFields().size());

        ReferenceTypeImpl rtClassDeclaration = new ReferenceTypeImpl(classDeclaration, typeSolver);

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
    public void testGetAllStaticFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedFieldDeclaration> allFields = constructorDeclaration.getAllStaticFields();
        assertEquals(3, allFields.size());

        ResolvedFieldDeclaration fieldDeclaration = null;

        fieldDeclaration = allFields.get(0);
        assertEquals("NODE_BY_BEGIN_POSITION", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(1);
        assertEquals("ABSOLUTE_BEGIN_LINE", fieldDeclaration.getName());

        fieldDeclaration = allFields.get(2);
        assertEquals("ABSOLUTE_END_LINE", fieldDeclaration.getName());
    }

    @Test
    public void testGetAllNonStaticFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedFieldDeclaration> allFields = constructorDeclaration.getAllNonStaticFields();
        assertEquals(13, allFields.size());

        ResolvedFieldDeclaration fieldDeclaration = null;

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
    public void testGetDeclaredFields() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        List<ResolvedFieldDeclaration> allFields = constructorDeclaration.getDeclaredFields();
        assertEquals(6, allFields.size());

        ResolvedFieldDeclaration fieldDeclaration = null;

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
    public void testGetDeclaredMethods() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        Set<ResolvedMethodDeclaration> allMethods = constructorDeclaration.getDeclaredMethods();
        assertEquals(20, allMethods.size());

        List<ResolvedMethodDeclaration> sortedMethods = allMethods.stream()
                .sorted((o1, o2) -> o1.getQualifiedSignature().compareTo(o2.getQualifiedSignature()))
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
    public void testGetAllMethods() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        Set<MethodUsage> allMethods = constructorDeclaration.getAllMethods();

        List<MethodUsage> sortedMethods = allMethods.stream()
                .sorted((o1, o2) -> o1.getQualifiedSignature().compareTo(o2.getQualifiedSignature()))
                .collect(Collectors.toList());

        List<String> signatures = sortedMethods.stream().map(m -> m.getQualifiedSignature()).collect(Collectors.toList());

        assertEquals(ImmutableList.of("com.github.javaparser.ast.Node.addOrphanComment(com.github.javaparser.ast.comments.Comment)",
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
                "java.lang.Object.wait(long, int)"), signatures);
    }

    ///
    /// Test constructors
    ///

    @Test
    public void testGetConstructors() {
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
    public void testSolveMethodExisting() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<ResolvedMethodDeclaration> res = null;

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
    public void testSolveMethodNotExisting() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<ResolvedMethodDeclaration> res = null;

        res = constructorDeclaration.solveMethod("unexistingMethod", ImmutableList.of());
        assertEquals(false, res.isSolved());

        res = constructorDeclaration.solveMethod("isStatic", ImmutableList.of(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(false, res.isSolved());
    }

    @Test
    public void testSolveMethodNotExistingBecauseOfTypeParameters() {
        JavaParserClassDeclaration constructorDeclaration = (JavaParserClassDeclaration) typeSolverNewCode.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        SymbolReference<ResolvedMethodDeclaration> res = null;

        ResolvedReferenceType stringType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(String.class, typeSolverNewCode);
        ResolvedReferenceType rawClassType = (ResolvedReferenceType) ReflectionFactory.typeUsageFor(Class.class, typeSolverNewCode);
        ResolvedReferenceType classOfStringType = (ResolvedReferenceType) rawClassType.replaceTypeVariables(rawClassType.getTypeDeclaration().getTypeParameters().get(0), stringType);
        res = constructorDeclaration.solveMethod("isThrows", ImmutableList.of(classOfStringType));
        assertEquals(false, res.isSolved());
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
    public void testHasDirectlyAnnotation() throws IOException, ParseException {
        TypeSolver typeSolver = new ReflectionTypeSolver();

        CompilationUnit cu = JavaParser.parse(adaptPath(new File("src/test/resources/Annotations.java.txt")));

        JavaParserClassDeclaration ca = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CA"), typeSolver);
        assertEquals(true, ca.hasDirectlyAnnotation("foo.bar.MyAnnotation"));
        assertEquals(false, ca.hasDirectlyAnnotation("foo.bar.MyAnnotation2"));
        assertEquals(false, ca.hasDirectlyAnnotation("MyAnnotation"));
        assertEquals(false, ca.hasDirectlyAnnotation("foo.bar.MyUnexistingAnnotation"));

        JavaParserClassDeclaration cb = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CB"), typeSolver);
        assertEquals(false, cb.hasDirectlyAnnotation("foo.bar.MyAnnotation"));
        assertEquals(true, cb.hasDirectlyAnnotation("foo.bar.MyAnnotation2"));
        assertEquals(false, cb.hasDirectlyAnnotation("MyAnnotation"));
        assertEquals(false, cb.hasDirectlyAnnotation("foo.bar.MyUnexistingAnnotation"));
    }

    // hasAnnotation

    @Test
    public void testHasAnnotation() throws IOException, ParseException {
        TypeSolver typeSolver = new ReflectionTypeSolver();

        CompilationUnit cu = JavaParser.parse(adaptPath(new File("src/test/resources/Annotations.java.txt")));

        JavaParserClassDeclaration ca = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CA"), typeSolver);
        assertEquals(true, ca.hasAnnotation("foo.bar.MyAnnotation"));
        assertEquals(false, ca.hasAnnotation("foo.bar.MyAnnotation2"));
        assertEquals(false, ca.hasAnnotation("MyAnnotation"));
        assertEquals(false, ca.hasAnnotation("foo.bar.MyUnexistingAnnotation"));

        JavaParserClassDeclaration cb = new JavaParserClassDeclaration(Navigator.demandClass(cu, "CB"), typeSolver);
        assertEquals(true, cb.hasAnnotation("foo.bar.MyAnnotation"));
        assertEquals(true, cb.hasAnnotation("foo.bar.MyAnnotation2"));
        assertEquals(false, cb.hasAnnotation("MyAnnotation"));
        assertEquals(false, cb.hasAnnotation("foo.bar.MyUnexistingAnnotation"));
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
}
