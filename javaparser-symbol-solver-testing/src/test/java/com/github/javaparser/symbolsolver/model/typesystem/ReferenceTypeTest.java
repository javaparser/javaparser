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

package com.github.javaparser.symbolsolver.model.typesystem;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StringProvider;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.Serializable;
import java.nio.Buffer;
import java.nio.CharBuffer;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertThrows;

class ReferenceTypeTest {

    private ReferenceTypeImpl listOfA;
    private ReferenceTypeImpl listOfStrings;
    private ReferenceTypeImpl linkedListOfString;
    private ReferenceTypeImpl collectionOfString;
    private ReferenceTypeImpl listOfWildcardExtendsString;
    private ReferenceTypeImpl listOfWildcardSuperString;
    private ReferenceTypeImpl object;
    private ReferenceTypeImpl string;
    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
        object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        listOfA = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ResolvedTypeVariable(ResolvedTypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList()))), typeSolver);
        listOfStrings = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);
        linkedListOfString = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(LinkedList.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);
        collectionOfString = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(Collection.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);
        listOfWildcardExtendsString = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(ResolvedWildcard.extendsBound(string)), typeSolver);
        listOfWildcardSuperString = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(ResolvedWildcard.superBound(string)), typeSolver);
    }

    @Test
    void testDerivationOfTypeParameters() {
        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        ReferenceTypeImpl ref1 = new ReferenceTypeImpl(typeSolver.solveType(LinkedList.class.getCanonicalName()), typeSolver);
        assertEquals(1, ref1.typeParametersValues().size());
        assertEquals(true, ref1.typeParametersValues().get(0).isTypeVariable());
        assertEquals("E", ref1.typeParametersValues().get(0).asTypeParameter().getName());
    }

    @Test
    void testIsArray() {
        assertEquals(false, object.isArray());
        assertEquals(false, string.isArray());
        assertEquals(false, listOfA.isArray());
        assertEquals(false, listOfStrings.isArray());
    }

    @Test
    void testIsPrimitive() {
        assertEquals(false, object.isPrimitive());
        assertEquals(false, string.isPrimitive());
        assertEquals(false, listOfA.isPrimitive());
        assertEquals(false, listOfStrings.isPrimitive());
    }

    @Test
    void testIsNull() {
        assertEquals(false, object.isNull());
        assertEquals(false, string.isNull());
        assertEquals(false, listOfA.isNull());
        assertEquals(false, listOfStrings.isNull());
    }

    @Test
    void testIsReference() {
        assertEquals(true, object.isReference());
        assertEquals(true, string.isReference());
        assertEquals(true, listOfA.isReference());
        assertEquals(true, listOfStrings.isReference());
    }

    @Test
    void testIsReferenceType() {
        assertEquals(true, object.isReferenceType());
        assertEquals(true, string.isReferenceType());
        assertEquals(true, listOfA.isReferenceType());
        assertEquals(true, listOfStrings.isReferenceType());
    }

    @Test
    void testIsVoid() {
        assertEquals(false, object.isVoid());
        assertEquals(false, string.isVoid());
        assertEquals(false, listOfA.isVoid());
        assertEquals(false, listOfStrings.isVoid());
    }

    @Test
    void testIsTypeVariable() {
        assertEquals(false, object.isTypeVariable());
        assertEquals(false, string.isTypeVariable());
        assertEquals(false, listOfA.isTypeVariable());
        assertEquals(false, listOfStrings.isTypeVariable());
    }

    @Test
    void testAsReferenceTypeUsage() {
        assertTrue(object == object.asReferenceType());
        assertTrue(string == string.asReferenceType());
        assertTrue(listOfA == listOfA.asReferenceType());
        assertTrue(listOfStrings == listOfStrings.asReferenceType());
    }

    @Test
    void testAsTypeParameter() {
        assertThrows(UnsupportedOperationException.class, () -> object.asTypeParameter());
    }

    @Test
    void testAsArrayTypeUsage() {
        assertThrows(UnsupportedOperationException.class, () -> object.asArrayType());
    }

    @Test
    void testAsDescribe() {
        assertEquals("java.lang.Object", object.describe());
        assertEquals("java.lang.String", string.describe());
        assertEquals("java.util.List<A>", listOfA.describe());
        assertEquals("java.util.List<java.lang.String>", listOfStrings.describe());
    }

    @Test
    void testReplaceParam() {
        ResolvedTypeParameterDeclaration tpA = ResolvedTypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList());
        assertTrue(object == object.replaceTypeVariables(tpA, object));
        assertTrue(string == string.replaceTypeVariables(tpA, object));
        assertEquals(listOfStrings, listOfStrings.replaceTypeVariables(tpA, object));
        assertEquals(listOfStrings, listOfA.replaceTypeVariables(tpA, string));
    }

    @Test
    void testIsAssignableBySimple() {
        assertEquals(true, object.isAssignableBy(string));
        assertEquals(false, string.isAssignableBy(object));
        assertEquals(false, listOfStrings.isAssignableBy(listOfA));
        assertEquals(false, listOfA.isAssignableBy(listOfStrings));

        assertEquals(false, object.isAssignableBy(ResolvedVoidType.INSTANCE));
        assertEquals(false, string.isAssignableBy(ResolvedVoidType.INSTANCE));
        assertEquals(false, listOfStrings.isAssignableBy(ResolvedVoidType.INSTANCE));
        assertEquals(false, listOfA.isAssignableBy(ResolvedVoidType.INSTANCE));

        assertEquals(true, object.isAssignableBy(NullType.INSTANCE));
        assertEquals(true, string.isAssignableBy(NullType.INSTANCE));
        assertEquals(true, listOfStrings.isAssignableBy(NullType.INSTANCE));
        assertEquals(true, listOfA.isAssignableBy(NullType.INSTANCE));
    }

    @Test
    void testIsAssignableByBoxedPrimitive(){
        ResolvedReferenceType numberType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Number.class, typeSolver),typeSolver);
        ResolvedReferenceType intType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Integer.class, typeSolver),typeSolver);
        ResolvedReferenceType doubleType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Double.class, typeSolver),typeSolver);

        assertEquals(true,  numberType.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(true,  numberType.isAssignableBy(ResolvedPrimitiveType.DOUBLE));
        assertEquals(true,  numberType.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(true,  numberType.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(true,  numberType.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, numberType.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(true,  intType.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(true,  doubleType.isAssignableBy(ResolvedPrimitiveType.DOUBLE));
    }

    @Test
    void testIsAssignableByGenerics() {
        assertEquals(false, listOfStrings.isAssignableBy(listOfWildcardExtendsString));
        assertEquals(false, listOfStrings.isAssignableBy(listOfWildcardExtendsString));
        assertEquals(true, listOfWildcardExtendsString.isAssignableBy(listOfStrings));
        assertEquals(false, listOfWildcardExtendsString.isAssignableBy(listOfWildcardSuperString));
        assertEquals(true, listOfWildcardSuperString.isAssignableBy(listOfStrings));
        assertEquals(false, listOfWildcardSuperString.isAssignableBy(listOfWildcardExtendsString));
    }

    @Test
    void testIsAssignableByGenericsInheritance() {
        assertEquals(true, collectionOfString.isAssignableBy(collectionOfString));
        assertEquals(true, collectionOfString.isAssignableBy(listOfStrings));
        assertEquals(true, collectionOfString.isAssignableBy(linkedListOfString));

        assertEquals(false, listOfStrings.isAssignableBy(collectionOfString));
        assertEquals(true, listOfStrings.isAssignableBy(listOfStrings));
        assertEquals(true, listOfStrings.isAssignableBy(linkedListOfString));

        assertEquals(false, linkedListOfString.isAssignableBy(collectionOfString));
        assertEquals(false, linkedListOfString.isAssignableBy(listOfStrings));
        assertEquals(true, linkedListOfString.isAssignableBy(linkedListOfString));
    }

    @Test
    void testGetAllAncestorsConsideringTypeParameters() {
        assertTrue(linkedListOfString.getAllAncestors().contains(object));
        assertTrue(linkedListOfString.getAllAncestors().contains(listOfStrings));
        assertTrue(linkedListOfString.getAllAncestors().contains(collectionOfString));
        assertFalse(linkedListOfString.getAllAncestors().contains(listOfA));
    }

    class Foo {

    }

    class Bar extends Foo {

    }

    class Bazzer<A, B, C> {

    }

    class MoreBazzing<A, B> extends Bazzer<B, String, A> {

    }

    @Test
    void testGetAllAncestorsConsideringGenericsCases() {
        ReferenceTypeImpl foo = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver), typeSolver);
        ReferenceTypeImpl bar = new ReferenceTypeImpl(new ReflectionClassDeclaration(Bar.class, typeSolver), typeSolver);
        ReferenceTypeImpl left, right;

        //YES MoreBazzing<Foo, Bar> e1 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(foo, bar), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES MoreBazzing<? extends Foo, Bar> e2 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(ResolvedWildcard.extendsBound(foo), bar), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES MoreBazzing<Foo, ? extends Bar> e3 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(foo, ResolvedWildcard.extendsBound(bar)), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES MoreBazzing<? extends Foo, ? extends Foo> e4 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(ResolvedWildcard.extendsBound(foo), ResolvedWildcard.extendsBound(foo)), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES MoreBazzing<? extends Foo, ? extends Foo> e5 = new MoreBazzing<Bar, Bar>();
        left = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(ResolvedWildcard.extendsBound(foo), ResolvedWildcard.extendsBound(foo)), typeSolver);
        right = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(bar, bar), typeSolver);
        assertEquals(true, left.isAssignableBy(right));

        //YES Bazzer<Object, String, String> e6 = new MoreBazzing<String, Object>();
        left = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                ImmutableList.of(object, string, string), typeSolver);
        right = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(string, object), typeSolver);

        // To debug the following
        List<ResolvedReferenceType> ancestors = right.getAllAncestors();
        ResolvedReferenceType moreBazzingAncestor = ancestors.stream().filter(a -> a.getQualifiedName().endsWith("Bazzer")).findFirst().get();

        assertEquals(true, left.isAssignableBy(right));

        //YES Bazzer<String,String,String> e7 = new MoreBazzing<String, String>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(string, string, string), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(string, string), typeSolver))
        );

        //YES Bazzer<Bar,String,Foo> e8 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar, string, foo), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES Bazzer<Foo,String,Bar> e9 = new MoreBazzing<Bar, Foo>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(foo, string, bar), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo), typeSolver))
        );

        //NO Bazzer<Bar,String,Foo> n1 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar, string, foo), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo), typeSolver))
        );

        //NO Bazzer<Bar,String,Bar> n2 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar, string, foo), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo), typeSolver))
        );

        //NO Bazzer<Foo,Object,Bar> n3 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(foo, object, bar), typeSolver)
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo), typeSolver))
        );
    }

    @Test
    void charSequenceIsAssignableToObject() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ReferenceTypeImpl charSequence = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(CharSequence.class, typeSolver), typeSolver);
        ReferenceTypeImpl object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        assertEquals(false, charSequence.isAssignableBy(object));
        assertEquals(true, object.isAssignableBy(charSequence));
    }

    @Test
    void testGetFieldTypeExisting() {
        class Foo<A> {
            List<A> elements;
        }

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ReferenceTypeImpl ref = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver), typeSolver);

        assertEquals(true, ref.getFieldType("elements").isPresent());
        assertEquals(true, ref.getFieldType("elements").get().isReferenceType());
        assertEquals(List.class.getCanonicalName(), ref.getFieldType("elements").get().asReferenceType().getQualifiedName());
        assertEquals(1, ref.getFieldType("elements").get().asReferenceType().typeParametersValues().size());
        assertEquals(true, ref.getFieldType("elements").get().asReferenceType().typeParametersValues().get(0).isTypeVariable());
        assertEquals("A", ref.getFieldType("elements").get().asReferenceType().typeParametersValues().get(0).asTypeParameter().getName());

        ref = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)),
                typeSolver);

        assertEquals(true, ref.getFieldType("elements").isPresent());
        assertEquals(true, ref.getFieldType("elements").get().isReferenceType());
        assertEquals(List.class.getCanonicalName(), ref.getFieldType("elements").get().asReferenceType().getQualifiedName());
        assertEquals(1, ref.getFieldType("elements").get().asReferenceType().typeParametersValues().size());
        assertEquals(true, ref.getFieldType("elements").get().asReferenceType().typeParametersValues().get(0).isReferenceType());
        assertEquals(String.class.getCanonicalName(), ref.getFieldType("elements").get().asReferenceType().typeParametersValues().get(0).asReferenceType().getQualifiedName());
    }

    @Test
    void testGetFieldTypeUnexisting() {
        class Foo<A> {
            List<A> elements;
        }

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ReferenceTypeImpl ref = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver), typeSolver);

        assertEquals(false, ref.getFieldType("bar").isPresent());

        ref = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)),
                typeSolver);

        assertEquals(false, ref.getFieldType("bar").isPresent());
    }

    @Test
    void testTypeParamValue() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        ResolvedClassDeclaration abstractList = new ReflectionClassDeclaration(AbstractList.class, typeResolver);
        ResolvedClassDeclaration abstractCollection = new ReflectionClassDeclaration(AbstractCollection.class, typeResolver);
        ResolvedInterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
        ResolvedInterfaceDeclaration collection = new ReflectionInterfaceDeclaration(Collection.class, typeResolver);
        ResolvedInterfaceDeclaration iterable = new ReflectionInterfaceDeclaration(Iterable.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver), typeResolver);
        ResolvedReferenceType arrayListOfString = new ReferenceTypeImpl(arraylist, ImmutableList.of(string), typeResolver);
        assertEquals(Optional.of(string), arrayListOfString.typeParamValue(arraylist.getTypeParameters().get(0)));
        assertEquals(Optional.of(string), arrayListOfString.typeParamValue(abstractList.getTypeParameters().get(0)));
        assertEquals(Optional.of(string), arrayListOfString.typeParamValue(abstractCollection.getTypeParameters().get(0)));
        assertEquals(Optional.of(string), arrayListOfString.typeParamValue(list.getTypeParameters().get(0)));
        assertEquals(Optional.of(string), arrayListOfString.typeParamValue(collection.getTypeParameters().get(0)));
        assertEquals(Optional.of(string), arrayListOfString.typeParamValue(iterable.getTypeParameters().get(0)));
    }

    @Test
    void testGetAllAncestorsOnRawType() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        ResolvedReferenceType rawArrayList = new ReferenceTypeImpl(arraylist, typeResolver);

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        rawArrayList.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(9, ancestors.size());

        ResolvedTypeVariable tv = new ResolvedTypeVariable(arraylist.getTypeParameters().get(0));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(RandomAccess.class, typeResolver), typeResolver), ancestors.get("java.util.RandomAccess"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractCollection.class, typeResolver), ImmutableList.of(tv), typeResolver), ancestors.get("java.util.AbstractCollection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeResolver), ImmutableList.of(tv), typeResolver), ancestors.get("java.util.List"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Cloneable.class, typeResolver), typeResolver), ancestors.get("java.lang.Cloneable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(tv), typeResolver), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractList.class, typeResolver), ImmutableList.of(tv), typeResolver), ancestors.get("java.util.AbstractList"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver), typeResolver), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(tv), typeResolver), ancestors.get("java.lang.Iterable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Serializable.class, typeResolver), typeResolver), ancestors.get("java.io.Serializable"));
    }

    @Test
    void testGetAllAncestorsOnTypeWithSpecifiedTypeParametersForInterface() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedInterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver), typeResolver);
        ResolvedReferenceType listOfString = new ReferenceTypeImpl(list, ImmutableList.of(string), typeResolver);

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        listOfString.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(3, ancestors.size());

        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver), typeResolver), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.lang.Iterable"));
    }

    @Test
    void testGetAllAncestorsOnTypeWithSpecifiedTypeParametersForClassAbstractCollection() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration abstractCollection = new ReflectionClassDeclaration(AbstractCollection.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver), typeResolver);
        ResolvedReferenceType abstractCollectionOfString = new ReferenceTypeImpl(abstractCollection, ImmutableList.of(string), typeResolver);

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        abstractCollectionOfString.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(3, ancestors.size());

        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver), typeResolver), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.lang.Iterable"));
    }

    @Test
    void testGetAllAncestorsOnTypeWithSpecifiedTypeParametersForClassAbstractList() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration abstractList = new ReflectionClassDeclaration(AbstractList.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver), typeResolver);
        ResolvedReferenceType abstractListOfString = new ReferenceTypeImpl(abstractList, ImmutableList.of(string), typeResolver);

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        abstractListOfString.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(5, ancestors.size());

        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractCollection.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.AbstractCollection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.List"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver), typeResolver), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.lang.Iterable"));
    }

    @Test
    void testGetAllAncestorsOnTypeWithSpecifiedTypeParametersForClassArrayList() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver), typeResolver);
        ResolvedReferenceType arrayListOfString = new ReferenceTypeImpl(arraylist, ImmutableList.of(string), typeResolver);

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        arrayListOfString.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(9, ancestors.size());

        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(RandomAccess.class, typeResolver), typeResolver), ancestors.get("java.util.RandomAccess"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractCollection.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.AbstractCollection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.List"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Cloneable.class, typeResolver), typeResolver), ancestors.get("java.lang.Cloneable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractList.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.util.AbstractList"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver), typeResolver), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(string), typeResolver), ancestors.get("java.lang.Iterable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Serializable.class, typeResolver), typeResolver), ancestors.get("java.io.Serializable"));
    }

    @Test
    void testTypeParametersValues() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedReferenceType stream = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Stream.class, typeResolver), typeResolver);
        assertEquals(1, stream.typeParametersValues().size());
        assertEquals(new ResolvedTypeVariable(new ReflectionInterfaceDeclaration(Stream.class, typeResolver).getTypeParameters().get(0)), stream.typeParametersValues().get(0));
    }

    @Test
    void testReplaceTypeVariables() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedInterfaceDeclaration streamInterface = new ReflectionInterfaceDeclaration(Stream.class, typeResolver);
        ResolvedReferenceType stream = new ReferenceTypeImpl(streamInterface, typeResolver);

        ResolvedMethodDeclaration streamMap = streamInterface.getDeclaredMethods().stream().filter(m -> m.getName().equals("map")).findFirst().get();
        ResolvedTypeParameterDeclaration streamMapR = streamMap.findTypeParameter("T").get();
        ResolvedTypeVariable typeVariable = new ResolvedTypeVariable(streamMapR);
        stream = stream.deriveTypeParameters(stream.typeParametersMap().toBuilder().setValue(stream.getTypeDeclaration().getTypeParameters().get(0), typeVariable).build());

        ResolvedTypeParameterDeclaration tpToReplace = streamInterface.getTypeParameters().get(0);
        ResolvedType replaced = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver), typeResolver);

        ResolvedType streamReplaced = stream.replaceTypeVariables(tpToReplace, replaced);
        assertEquals("java.util.stream.Stream<java.lang.String>", streamReplaced.describe());
    }

    @Test
    void testReplaceTypeVariablesWithLambdaInBetween() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedInterfaceDeclaration streamInterface = new ReflectionInterfaceDeclaration(Stream.class, typeResolver);
        ResolvedReferenceType stream = new ReferenceTypeImpl(streamInterface, typeResolver);

        ResolvedMethodDeclaration streamMap = streamInterface.getDeclaredMethods().stream().filter(m -> m.getName().equals("map")).findFirst().get();
        ResolvedTypeParameterDeclaration streamMapR = streamMap.findTypeParameter("T").get();
        ResolvedTypeVariable typeVariable = new ResolvedTypeVariable(streamMapR);
        stream = stream.deriveTypeParameters(stream.typeParametersMap().toBuilder().setValue(stream.getTypeDeclaration().getTypeParameters().get(0), typeVariable).build());

        ResolvedTypeParameterDeclaration tpToReplace = streamInterface.getTypeParameters().get(0);
        ResolvedType replaced = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver), typeResolver);

        ResolvedType streamReplaced = stream.replaceTypeVariables(tpToReplace, replaced);
        assertEquals("java.util.stream.Stream<java.lang.String>", streamReplaced.describe());
    }

    @Test
    void testDirectAncestorsOfObject() {
        assertEquals(0, object.getDirectAncestors().size());
    }

    @Test
    void testDirectAncestorsOfInterface() {
        ResolvedReferenceType iterableOfString = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(Iterable.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);
        assertEquals(1, iterableOfString.getDirectAncestors().size());
        ResolvedReferenceType ancestor = iterableOfString.getDirectAncestors().get(0);
        assertEquals("java.lang.Object", ancestor.getQualifiedName());
        assertEquals(true, ancestor.getTypeParametersMap().isEmpty());
    }

    @Test
    void testDirectAncestorsOfInterfaceExtendingInterface() {
        assertEquals(2, collectionOfString.getDirectAncestors().size());
        ResolvedReferenceType ancestor1 = collectionOfString.getDirectAncestors().get(0);
        assertEquals("java.lang.Iterable", ancestor1.getQualifiedName());
        assertEquals(1, ancestor1.getTypeParametersMap().size());
        assertEquals("T", ancestor1.getTypeParametersMap().get(0).a.getName());
        assertEquals("java.lang.String", ancestor1.getTypeParametersMap().get(0).b.describe());
        ResolvedReferenceType ancestor2 = collectionOfString.getDirectAncestors().get(1);
        assertEquals("java.lang.Object", ancestor2.getQualifiedName());
        assertEquals(true, ancestor2.getTypeParametersMap().isEmpty());
    }

    @Test
    void testDirectAncestorsOfClassWithoutSuperClassOrInterfaces() {
        ResolvedReferenceType buffer = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(Buffer.class, typeSolver), typeSolver);
        Set<String> ancestors = buffer.getDirectAncestors().stream().map(a -> a.describe()).collect(Collectors.toSet());
        assertEquals(new HashSet<>(Arrays.asList("java.lang.Object")), ancestors);
    }

    @Test
    void testDirectAncestorsOfObjectClass() {
        ResolvedReferenceType object = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        Set<String> ancestors = object.getDirectAncestors().stream().map(a -> a.describe()).collect(Collectors.toSet());
        assertEquals(new HashSet<>(), ancestors);
    }

    @Test
    void testDirectAncestorsOfClassWithSuperClass() {
        ResolvedReferenceType charbuffer = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(CharBuffer.class, typeSolver), typeSolver);
        Set<String> ancestors = charbuffer.getDirectAncestors().stream().map(a -> a.describe()).collect(Collectors.toSet());
        assertEquals(new HashSet<>(Arrays.asList("java.lang.CharSequence", "java.lang.Appendable",
                "java.nio.Buffer", "java.lang.Readable", "java.lang.Comparable<java.nio.CharBuffer>")), ancestors);
    }

    @Test
    void testDirectAncestorsOfClassWithInterfaces() {
        Set<String> ancestors = string.getDirectAncestors().stream().map(a -> a.describe()).collect(Collectors.toSet());
        assertEquals(new HashSet<>(Arrays.asList("java.lang.CharSequence",
                "java.lang.Object",
                "java.lang.Comparable<java.lang.String>",
                "java.io.Serializable")), ancestors);
    }

    @Test
    void testDeclaredFields() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        String code = "class A { private int i; char c; public long l; } class B extends A { private float f; boolean b; };";
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));

        CompilationUnit cu = new JavaParser(parserConfiguration)
                .parse(ParseStart.COMPILATION_UNIT, new StringProvider(code)).getResult().get();

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        ClassOrInterfaceDeclaration classB = cu.getClassByName("B").get();

        ResolvedReferenceType rtA = new ReferenceTypeImpl(classA.resolve(), typeSolver);
        ResolvedReferenceType rtB = new ReferenceTypeImpl(classB.resolve(), typeSolver);

        assertEquals(3, rtA.getDeclaredFields().size());
        assertTrue(rtA.getDeclaredFields().stream().anyMatch(f -> f.getName().equals("i")));
        assertTrue(rtA.getDeclaredFields().stream().anyMatch(f -> f.getName().equals("c")));
        assertTrue(rtA.getDeclaredFields().stream().anyMatch(f -> f.getName().equals("l")));

        assertEquals(2, rtB.getDeclaredFields().size());
        assertTrue(rtB.getDeclaredFields().stream().anyMatch(f -> f.getName().equals("f")));
        assertTrue(rtB.getDeclaredFields().stream().anyMatch(f -> f.getName().equals("b")));
    }

    @Test
    void testGetAllFieldsVisibleToInheritors() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        String code = "class A { private int i; char c; public long l; } class B extends A { private float f; boolean b; };";
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setSymbolResolver(new JavaSymbolSolver(typeSolver));

        CompilationUnit cu = new JavaParser(parserConfiguration)
                .parse(ParseStart.COMPILATION_UNIT, new StringProvider(code)).getResult().get();

        ClassOrInterfaceDeclaration classA = cu.getClassByName("A").get();
        ClassOrInterfaceDeclaration classB = cu.getClassByName("B").get();

        ResolvedReferenceType rtA = new ReferenceTypeImpl(classA.resolve(), typeSolver);
        ResolvedReferenceType rtB = new ReferenceTypeImpl(classB.resolve(), typeSolver);

        assertEquals(2, rtA.getAllFieldsVisibleToInheritors().size());
        assertTrue(rtA.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("c")));
        assertTrue(rtA.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("l")));

        assertEquals(3, rtB.getAllFieldsVisibleToInheritors().size());
        assertTrue(rtB.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("c")));
        assertTrue(rtB.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("l")));
        assertTrue(rtB.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("b")));
    }
}
