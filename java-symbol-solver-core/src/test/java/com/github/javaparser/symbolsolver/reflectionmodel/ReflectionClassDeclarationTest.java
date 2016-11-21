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

import com.github.javaparser.symbolsolver.model.declarations.*;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceType;
import com.github.javaparser.symbolsolver.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.symbolsolver.model.typesystem.TypeVariable;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.junit.Test;

import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ReflectionClassDeclarationTest {
    
    private TypeSolver typeResolver = new ReflectionTypeSolver(false);

    @Test
    public void testIsClass() {
        class Foo<E> {
            E field;
        }
        class Bar extends Foo<String> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals(true, foo.isClass());
        assertEquals(true, bar.isClass());
    }

    @Test
    public void testGetSuperclassSimpleImplicit() {
        class Foo<E> {
            E field;
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);

        assertEquals(Object.class.getCanonicalName(), foo.getSuperClass().getQualifiedName());
        assertEquals(Collections.emptyList(), foo.getSuperClass().typeParametersValues());
    }

    @Test
    public void testGetSuperclassSimple() {
        class Bar {
        }
        class Foo<E> extends Bar {
            E field;
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);

        assertEquals("Bar", foo.getSuperClass().getTypeDeclaration().getName());
        assertEquals(Collections.emptyList(), foo.getSuperClass().typeParametersValues());
    }

    @Test
    public void testGetSuperclassWithGenericSimple() {
        class Foo<E> {
            E field;
        }
        class Bar extends Foo<String> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals("Foo", bar.getSuperClass().getTypeDeclaration().getName());
        assertEquals(1, bar.getSuperClass().typeParametersValues().size());
        assertEquals(String.class.getCanonicalName(), bar.getSuperClass().typeParametersValues().get(0).asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetSuperclassWithGenericInheritanceSameName() {
        class Foo<E> {
            E field;
        }
        class Bar<E> extends Foo<E> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals("Foo", bar.getSuperClass().getTypeDeclaration().getName());
        assertEquals(1, bar.getSuperClass().typeParametersValues().size());
        assertEquals(true, bar.getSuperClass().typeParametersValues().get(0).isTypeVariable());
        assertEquals("E", bar.getSuperClass().typeParametersValues().get(0).asTypeParameter().getName());
        assertEquals(true, bar.getSuperClass().typeParametersValues().get(0).asTypeParameter().declaredOnType());
        assertEquals(false, bar.getSuperClass().typeParametersValues().get(0).asTypeParameter().declaredOnMethod());
        assertTrue(bar.getSuperClass().typeParametersValues().get(0).asTypeParameter().getQualifiedName().endsWith("Bar.E"));
    }

    @Test
    public void testGetSuperclassWithGenericInheritanceDifferentName() {
        class Foo<E> {
            E field;
        }
        class Bar extends Foo<String> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ClassDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ClassDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        assertEquals(true, foo.isClass());
        assertEquals(true, bar.isClass());
    }

    @Test
    public void testGetFieldDeclarationTypeVariableInheritance() {
        class Foo<E> {
            E field;
        }
        class Bar extends Foo<String> {
        }

        TypeSolver typeResolver = new ReflectionTypeSolver();

        ReferenceTypeDeclaration foo = new ReflectionClassDeclaration(Foo.class, typeResolver);
        ReferenceTypeDeclaration bar = new ReflectionClassDeclaration(Bar.class, typeResolver);

        FieldDeclaration fooField = foo.getField("field");
        assertEquals(true, fooField.getType().isTypeVariable());
        assertEquals("E", fooField.getType().asTypeParameter().getName());

        FieldDeclaration barField = bar.getField("field");
        assertEquals(true, barField.getType().isReferenceType());
        assertEquals(String.class.getCanonicalName(), barField.getType().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetDeclaredMethods() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ReferenceTypeDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
        List<MethodDeclaration> methods = string.getDeclaredMethods().stream()
                .filter(m -> m.accessLevel() != AccessLevel.PRIVATE && m.accessLevel() != AccessLevel.PACKAGE_PROTECTED)
                .sorted((a, b) -> a.getName().compareTo(b.getName()))
                .collect(Collectors.toList());
        assertEquals(67, methods.size());
        assertEquals("charAt", methods.get(0).getName());
        assertEquals(false, methods.get(0).isAbstract());
        assertEquals(1, methods.get(0).getNumberOfParams());
        assertEquals("int", methods.get(0).getParam(0).getType().describe());
        assertEquals("concat", methods.get(6).getName());
        assertEquals(false, methods.get(6).isAbstract());
        assertEquals(1, methods.get(6).getNumberOfParams());
        assertEquals("java.lang.String", methods.get(6).getParam(0).getType().describe());
    }

    @Test
    public void testGetInterfaces() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        // Serializable, Cloneable, List<E>, RandomAccess
        assertEquals(ImmutableSet.of(Serializable.class.getCanonicalName(),
                Cloneable.class.getCanonicalName(),
                List.class.getCanonicalName(),
                RandomAccess.class.getCanonicalName()),
                arraylist.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllInterfaces() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
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
    public void testGetAllSuperclasses() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        assertEquals(ImmutableSet.of(Object.class.getCanonicalName(),
                AbstractCollection.class.getCanonicalName(),
                AbstractList.class.getCanonicalName()),
                arraylist.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
        ClassDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
        assertEquals(ImmutableSet.of(Object.class.getCanonicalName()),
                string.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetQualifiedName() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        assertEquals("java.util.ArrayList", arraylist.getQualifiedName());
        ClassDeclaration string = new ReflectionClassDeclaration(String.class, typeResolver);
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
    public void testGetAllFields() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        assertEquals(ImmutableSet.of("modCount", "serialVersionUID", "MAX_ARRAY_SIZE", "size", "elementData", "EMPTY_ELEMENTDATA", "DEFAULTCAPACITY_EMPTY_ELEMENTDATA", "DEFAULT_CAPACITY"),
                arraylist.getAllFields().stream().map(Declaration::getName).collect(Collectors.toSet()));
    }

    ///
    /// Test ancestors
    ///    

    @Test
    public void testAllAncestors() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        Map<String, ReferenceType> ancestors = new HashMap<>();
        arraylist.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(9, ancestors.size());

        TypeVariable typeVariable = new TypeVariable(arraylist.getTypeParameters().get(0));
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
    public void testGetSuperclassWithoutTypeParameters() {
        ReflectionClassDeclaration compilationUnit = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals("com.github.javaparser.ast.Node", compilationUnit.getSuperClass().getQualifiedName());
    }

    @Test
    public void testGetSuperclassWithTypeParameters() {
        ReflectionClassDeclaration compilationUnit = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", compilationUnit.getSuperClass().getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", compilationUnit.getSuperClass().typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAllSuperclassesWithoutTypeParameters() {
        ReflectionClassDeclaration cu = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.Node", "java.lang.Object"), cu.getAllSuperClasses().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllSuperclassesWithTypeParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(3, constructorDeclaration.getAllSuperClasses().size());
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.body.BodyDeclaration")));
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("com.github.javaparser.ast.Node")));
        assertEquals(true, constructorDeclaration.getAllSuperClasses().stream().anyMatch(s -> s.getQualifiedName().equals("java.lang.Object")));

        ReferenceType ancestor = null;

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
        ReflectionClassDeclaration compilationUnit = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of(), compilationUnit.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        ReflectionClassDeclaration coid = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.nodeTypes.NodeWithExtends",
                "com.github.javaparser.ast.nodeTypes.NodeWithImplements",
                "com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters"),
                coid.getInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetInterfacesWithParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        System.out.println(constructorDeclaration.getInterfaces().stream().map(t -> t.getQualifiedName()).collect(Collectors.toList()));
        assertEquals(8, constructorDeclaration.getInterfaces().size());

        ReferenceType interfaze = null;

        interfaze = constructorDeclaration.getInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getInterfaces().get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAllInterfacesWithoutParameters() {
        ReflectionClassDeclaration compilationUnit = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.visitor.Visitable", "com.github.javaparser.ast.observing.Observable", "com.github.javaparser.HasParentNode"), compilationUnit.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));

        ReflectionClassDeclaration coid = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ClassOrInterfaceDeclaration");
        assertEquals(ImmutableSet.of("com.github.javaparser.ast.nodeTypes.NodeWithExtends",
                "com.github.javaparser.ast.nodeTypes.NodeWithAnnotations",
                "java.lang.Cloneable",
                "com.github.javaparser.HasParentNode",
                "com.github.javaparser.ast.visitor.Visitable",
                "com.github.javaparser.ast.nodeTypes.NodeWithImplements",
                "com.github.javaparser.ast.nodeTypes.NodeWithSimpleName",
                "com.github.javaparser.ast.nodeTypes.NodeWithModifiers",
                "com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc",
                "com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters",
                "com.github.javaparser.ast.nodeTypes.NodeWithMembers",
                "com.github.javaparser.ast.observing.Observable"), coid.getAllInterfaces().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllInterfacesWithParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(13, constructorDeclaration.getAllInterfaces().size());

        ReferenceType interfaze = null;

        interfaze = constructorDeclaration.getAllInterfaces().get(0);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(7);
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(8);
        assertEquals("java.lang.Cloneable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(9);
        assertEquals("com.github.javaparser.HasParentNode", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.Node", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.HasParentNode.T").get().asReferenceType().getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(10);
        assertEquals("com.github.javaparser.ast.observing.Observable", interfaze.getQualifiedName());


        interfaze = constructorDeclaration.getAllInterfaces().get(11);
        assertEquals("com.github.javaparser.ast.visitor.Visitable", interfaze.getQualifiedName());

        interfaze = constructorDeclaration.getAllInterfaces().get(12);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", interfaze.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", interfaze.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.N").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAncestorsWithTypeParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(9, constructorDeclaration.getAncestors().size());

        ReferenceType ancestor = null;

        ancestor = constructorDeclaration.getAncestors().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(1);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(2);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(3);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(4);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(5);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(7);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAncestors().get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());
    }

    @Test
    public void testGetAllAncestorsWithoutTypeParameters() {
        ReflectionClassDeclaration cu = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.CompilationUnit");
        assertEquals(ImmutableSet.of("java.lang.Cloneable", "com.github.javaparser.ast.visitor.Visitable", "com.github.javaparser.ast.observing.Observable", "com.github.javaparser.ast.Node", "java.lang.Object", "com.github.javaparser.HasParentNode"), cu.getAllAncestors().stream().map(i -> i.getQualifiedName()).collect(Collectors.toSet()));
    }

    @Test
    public void testGetAllAncestorsWithTypeParameters() {
        ReflectionClassDeclaration constructorDeclaration = (ReflectionClassDeclaration) typeResolver.solveType("com.github.javaparser.ast.body.ConstructorDeclaration");
        assertEquals(16, constructorDeclaration.getAllAncestors().size());

        ReferenceType ancestor = null;

        ancestor = constructorDeclaration.getAllAncestors().get(0);
        assertEquals("com.github.javaparser.ast.body.BodyDeclaration", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.body.BodyDeclaration.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(1);
        assertEquals("com.github.javaparser.ast.Node", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(2);
        assertEquals("java.lang.Cloneable", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(3);
        assertEquals("com.github.javaparser.HasParentNode", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.Node", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.HasParentNode.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(4);
        assertEquals("com.github.javaparser.ast.observing.Observable", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(5);
        assertEquals("com.github.javaparser.ast.visitor.Visitable", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(6);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithAnnotations.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(7);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(8);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(9);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithDeclaration", ancestor.getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(10);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithSimpleName.T").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(11);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithModifiers", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithModifiers.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(12);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithParameters.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(13);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithThrowable", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithThrowable.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(14);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt.N").get().asReferenceType().getQualifiedName());

        ancestor = constructorDeclaration.getAllAncestors().get(15);
        assertEquals("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters", ancestor.getQualifiedName());
        assertEquals("com.github.javaparser.ast.body.ConstructorDeclaration", ancestor.typeParametersMap().getValueBySignature("com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters.N").get().asReferenceType().getQualifiedName());
    }
}
