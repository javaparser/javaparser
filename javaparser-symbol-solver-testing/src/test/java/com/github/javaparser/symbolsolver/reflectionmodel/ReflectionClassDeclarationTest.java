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

import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.junit.jupiter.api.Test;

import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

import static java.util.Comparator.*;
import static org.junit.jupiter.api.Assertions.*;

class ReflectionClassDeclarationTest extends AbstractSymbolResolutionTest {

    private TypeSolver typeResolver = new ReflectionTypeSolver(false);

    @Test
    void testIsClass() {
        class Foo<E> {
            E field;
        }
        class Bar extends Foo<String> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ResolvedClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals(true, foo.isClass());
        assertEquals(true, bar.isClass());
    }

    @Test
    void testGetSuperclassSimpleImplicit() {
        class Foo<E> {
            E field;
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);

        assertEquals(Object.class.getCanonicalName(), foo.getSuperClass().getQualifiedName());
        assertEquals(Collections.emptyList(), foo.getSuperClass().typeParametersValues());
    }

    @Test
    void testGetSuperclassSimple() {
        class Bar {
        }
        class Foo<E> extends Bar {
            E field;
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);

        assertEquals("Bar", foo.getSuperClass().getTypeDeclaration().getName());
        assertEquals(Collections.emptyList(), foo.getSuperClass().typeParametersValues());
    }

    @Test
    void testGetSuperclassWithGenericSimple() {
        class Foo<E> {
            E field;
        }
        class Bar extends Foo<String> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ResolvedClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals("Foo", bar.getSuperClass().getTypeDeclaration().getName());
        assertEquals(1, bar.getSuperClass().typeParametersValues().size());
        assertEquals(String.class.getCanonicalName(), bar.getSuperClass().typeParametersValues().get(0).asReferenceType().getQualifiedName());
    }

    @Test
    void testGetSuperclassWithGenericInheritanceSameName() {
        class Foo<E> {
            E field;
        }
        class Bar<E> extends Foo<E> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ResolvedClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals("Foo", bar.getSuperClass().getTypeDeclaration().getName());
        assertEquals(1, bar.getSuperClass().typeParametersValues().size());
        assertEquals(true, bar.getSuperClass().typeParametersValues().get(0).isTypeVariable());
        assertEquals("E", bar.getSuperClass().typeParametersValues().get(0).asTypeParameter().getName());
        assertEquals(true, bar.getSuperClass().typeParametersValues().get(0).asTypeParameter().declaredOnType());
        assertEquals(false, bar.getSuperClass().typeParametersValues().get(0).asTypeParameter().declaredOnMethod());
        assertTrue(bar.getSuperClass().typeParametersValues().get(0).asTypeParameter().getQualifiedName().endsWith("Bar.E"));
    }

    @Test
    void testGetSuperclassWithGenericInheritanceDifferentName() {
        class Foo<E> {
            E field;
        }
        class Bar extends Foo<String> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ResolvedClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals(true, foo.isClass());
        assertEquals(true, bar.isClass());
    }

    @Test
    void testGetFieldDeclarationTypeVariableInheritance() {
        class Foo<E> {
            E field;
        }
        class Bar extends Foo<String> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ResolvedReferenceTypeDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ResolvedReferenceTypeDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        ResolvedFieldDeclaration fooField = foo.getField("field");
        assertEquals(true, fooField.getType().isTypeVariable());
        assertEquals("E", fooField.getType().asTypeParameter().getName());

        ResolvedFieldDeclaration barField = bar.getField("field");
        assertEquals(true, barField.getType().isReferenceType());
        assertEquals(String.class.getCanonicalName(), barField.getType().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetDeclaredMethods() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedReferenceTypeDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
        List<ResolvedMethodDeclaration> methods = string.getDeclaredMethods().stream()
                .filter(m -> m.accessSpecifier() != AccessSpecifier.PRIVATE && m.accessSpecifier() != AccessSpecifier.PACKAGE_PRIVATE)
                .sorted((a, b) -> a.getName().compareTo(b.getName()))
                .collect(Collectors.toList());
        int foundCount = 0;
        for (ResolvedMethodDeclaration method : methods) {
            switch (method.getName()) {
                case "charAt":
                    assertFalse(method.isAbstract());
                    assertEquals(1, method.getNumberOfParams());
                    assertEquals("int", method.getParam(0).getType().describe());
                    foundCount++;
                    break;
                case "compareTo":
                    assertFalse(method.isAbstract());
                    assertEquals(1, method.getNumberOfParams());
                    assertEquals("java.lang.String", method.getParam(0).getType().describe());
                    foundCount++;
                    break;
                case "concat":
                    assertFalse(method.isAbstract());
                    assertEquals(1, method.getNumberOfParams());
                    assertEquals("java.lang.String", method.getParam(0).getType().describe());
                    foundCount++;
                    break;
            }
        }
        assertEquals(3, foundCount);
    }

    @Test
    void testGetConstructors() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedReferenceTypeDeclaration locale = new ReflectionClassDeclaration(ClassWithSyntheticConstructor.class, typeResolver);
        assertEquals(1, locale.getConstructors().size());
    }

    @Test
    void testGetInterfaces() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        // Serializable, Cloneable, List<E>, RandomAccess
        assertEquals(ImmutableSet.of(Serializable.class.getCanonicalName(),
                Cloneable.class.getCanonicalName(),
                List.class.getCanonicalName(),
                RandomAccess.class.getCanonicalName()),
                arraylist.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllInterfaces() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        // Serializable, Cloneable, Iterable<E>, Collection<E>, List<E>, RandomAccess
        assertEquals(ImmutableSet.of(Serializable.class.getCanonicalName(),
                Cloneable.class.getCanonicalName(),
                List.class.getCanonicalName(),
                RandomAccess.class.getCanonicalName(),
                Collection.class.getCanonicalName(),
                Iterable.class.getCanonicalName()),
                arraylist.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllSuperclasses() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        assertEquals(ImmutableSet.of(Object.class.getCanonicalName(),
                AbstractCollection.class.getCanonicalName(),
                AbstractList.class.getCanonicalName()),
                arraylist.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
        ResolvedClassDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
        assertEquals(ImmutableSet.of(Object.class.getCanonicalName()),
                string.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetPackageName() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        assertEquals("java.util", arraylist.getPackageName());
        ResolvedClassDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
        assertEquals("java.lang", string.getPackageName());
    }

    @Test
    void testGetClassName() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        assertEquals("ArrayList", arraylist.getClassName());
        ResolvedClassDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
        assertEquals("String", string.getClassName());
    }

    @Test
    void testGetQualifiedName() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        assertEquals("java.util.ArrayList", arraylist.getQualifiedName());
        ResolvedClassDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
        assertEquals("java.lang.String", string.getQualifiedName());
    }

    // solveMethod
    // isAssignableBy
    // canBeAssignedTo
    // hasField
    // solveSymbol
    // solveType
    // getDeclaredMethods
    // getAllMethods

    @Test
    void testGetAllFields() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        assertEquals(ImmutableSet.of("modCount", "serialVersionUID", "MAX_ARRAY_SIZE", "size", "elementData", "EMPTY_ELEMENTDATA", "DEFAULTCAPACITY_EMPTY_ELEMENTDATA", "DEFAULT_CAPACITY"),
                arraylist.getAllFields().stream().map(ResolvedDeclaration::getName).collect(Collectors.toSet()));
    }

    ///
    /// Test ancestors
    ///    

    @Test
    void testAllAncestors() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        arraylist.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(9, ancestors.size());

        ResolvedTypeVariable typeVariable = new ResolvedTypeVariable(arraylist.getTypeParameters().get(0));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(RandomAccess.class, typeResolver), typeResolver), ancestors.get("java.util.RandomAccess"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractCollection.class, typeResolver), ImmutableList.of(typeVariable), typeResolver), ancestors.get("java.util.AbstractCollection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeResolver), ImmutableList.of(typeVariable), typeResolver), ancestors.get("java.util.List"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Cloneable.class, typeResolver), typeResolver), ancestors.get("java.lang.Cloneable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(typeVariable), typeResolver), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractList.class, typeResolver), ImmutableList.of(typeVariable), typeResolver), ancestors.get("java.util.AbstractList"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver), typeResolver), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(typeVariable), typeResolver), ancestors.get("java.lang.Iterable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Serializable.class, typeResolver), typeResolver), ancestors.get("java.io.Serializable"));
    }

    @Test
    void testGetSuperclassWithoutTypeParameters() {
        ReflectionClassDeclaration compilationUnit = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().getQualifiedName());
    }

    @Test
    void testGetSuperclassWithTypeParameters() {
        ReflectionClassDeclaration compilationUnit = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals("com.github.javaparser.ast.body.CallableDeclaration", compilationUnit.getSuperClass().getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", compilationUnit.getSuperClass().typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.CallableDeclaration.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetAllSuperclassesWithoutTypeParameters() {
        ReflectionClassDeclaration cu = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllSuperclassesWithTypeParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(4, constructorDeclaration.getAllSuperClasses().size());
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.body.CallableDeclaration")));
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.body.BodyDeclaration")));
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.Node")));
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("java.lang.Object")));

        ResolvedReferenceType ancestor;

        ancestor = constructorDeclaration.getAllSuperClasses().get(0);
        assertEquals("com.github.javaparser.ast.body.CallableDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.CallableDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(1);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(2);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllSuperClasses().get(3);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());
    }

    @Test
    void testGetInterfacesWithoutParameters() {
        ReflectionClassDeclaration compilationUnit = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        ReflectionClassDeclaration coid = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");

        assertEquals(ImmutableSet.of("com.github.javaparser.ast.nodeTypes.NodeWithExtends",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier",
                "com.github.javaparser.ast.nodeTypes.NodeWithConstructors",
                "com.github.javaparser.ast.nodeTypes.NodeWithImplements",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAbstractModifier",
                "com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters",
                "com.github.javaparser.resolution.Resolvable"),
                coid.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetInterfacesWithParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        System.out.println(constructorDeclaration.getInterfaces().stream().map(t -> t.getQualifiedName()).collect(Collectors.toList()));
        assertEquals(8, constructorDeclaration.getInterfaces().size());

        ResolvedReferenceType interfaze;

        interfaze = constructorDeclaration.getInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(7);
        assertEquals("com.github.javaparser.resolution.Resolvable", interfaze.getQualifiedName());
    }

    @Test
    void testGetAllInterfacesWithoutParameters() {
        ReflectionClassDeclaration compilationUnit = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.visitor.Visitable", "com.github.javaparser.ast.observer.Observable",
                "com.github.javaparser.HasParentNode", "com.github.javaparser.ast.nodeTypes.NodeWithRange",
                "com.github.javaparser.ast.nodeTypes.NodeWithTokenRange").stream().sorted().collect(Collectors.toList()),
                compilationUnit.getAllInterfaces().stream().map(i -> i.getQualifiedName()).sorted().collect(Collectors.toList()));

        ReflectionClassDeclaration coid = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.nodeTypes.NodeWithExtends",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations",
                "java.lang.Cloneable",
                "com.github.javaparser.HasParentNode",
                "com.github.javaparser.ast.visitor.Visitable",
                "com.github.javaparser.ast.nodeTypes.NodeWithImplements",
                "com.github.javaparser.ast.nodeTypes.NodeWithSimpleName",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers",
                "com.github.javaparser.ast.nodeTypes.NodeWithJavadoc",
                "com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters",
                "com.github.javaparser.ast.nodeTypes.NodeWithMembers",
                "com.github.javaparser.ast.observer.Observable",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithProtectedModifier",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStaticModifier",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAbstractModifier",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPublicModifier",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers",
                "com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStrictfpModifier",
                "com.github.javaparser.ast.nodeTypes.NodeWithRange",
                "com.github.javaparser.ast.nodeTypes.NodeWithTokenRange",
                "com.github.javaparser.ast.nodeTypes.NodeWithConstructors",
                "com.github.javaparser.resolution.Resolvable"), coid.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllInterfacesWithParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        List<ResolvedReferenceType> interfaces = constructorDeclaration.getAllInterfaces();
        assertEquals(34, interfaces.size());

        ResolvedReferenceType interfaze;
        int i = 0;

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPublicModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPublicModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithProtectedModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithProtectedModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.resolution.Resolvable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("java.lang.Cloneable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.HasParentNode", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.Node", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.HasParentNode.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.observer.Observable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.visitor.Visitable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithRange", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.Node", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithRange.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTokenRange", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.Node", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTokenRange.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPublicModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPublicModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithProtectedModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithProtectedModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAbstractModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAbstractModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStaticModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStaticModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(i++);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStrictfpModifier", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStrictfpModifier.N").get().asReferenceType().getQualifiedName());
    }

    @Test
    void testGetAncestorsWithTypeParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(9, constructorDeclaration.getAncestors().size());

        ResolvedReferenceType ancestor;
        List<ResolvedReferenceType> ancestors = constructorDeclaration.getAncestors();
        ancestors.sort(comparing(ResolvedReferenceType::getQualifiedName));

        ancestor = ancestors.get(0);
        assertEquals("com.github.javaparser.ast.body.CallableDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.CallableDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.get(8);
        assertEquals("com.github.javaparser.resolution.Resolvable", ancestor.getQualifiedName());
    }

    @Test
    void testGetAllAncestorsWithoutTypeParameters() {
        ReflectionClassDeclaration cu = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.visitor.Visitable",
                "com.github.javaparser.ast.observer.Observable", "com.github.javaparser.ast.Node",
                "com.github.javaparser.ast.nodeTypes.NodeWithTokenRange", "java.lang.Object", "com.github.javaparser.HasParentNode",
                "com.github.javaparser.ast.nodeTypes.NodeWithRange"), cu.getAllAncestors().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    void testGetAllAncestorsWithTypeParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");

        ResolvedReferenceType ancestor;
        List<ResolvedReferenceType> ancestors = constructorDeclaration.getAllAncestors();
        ancestors.sort(comparing(ResolvedReferenceType::getQualifiedName));

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.HasParentNode", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.Node", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.HasParentNode.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.body.CallableDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.CallableDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavadoc.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithRange", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.Node", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithRange.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrownExceptions.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTokenRange", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.Node", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTokenRange.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAbstractModifier", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAbstractModifier.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPrivateModifier.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithProtectedModifier", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithProtectedModifier.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPublicModifier", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithPublicModifier.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStaticModifier", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStaticModifier.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStrictfpModifier", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStrictfpModifier.N").get().asReferenceType().getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.observer.Observable", ancestor.getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.ast.visitor.Visitable", ancestor.getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("com.github.javaparser.resolution.Resolvable", ancestor.getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("java.lang.Cloneable", ancestor.getQualifiedName());

        ancestor = ancestors.remove(0);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());

        assertTrue(ancestors.isEmpty());
    }

    public static class ClassWithSyntheticConstructor {

        private ClassWithSyntheticConstructor() {}

        public static ClassWithSyntheticConstructor newInstance() {
            return ClassWithSyntheticConstructorHelper.create();
        }

        private static class ClassWithSyntheticConstructorHelper {
            public static ClassWithSyntheticConstructor create() {
                return new ClassWithSyntheticConstructor();
            }
        }
    }

}
