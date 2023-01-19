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

package com.github.javaparser.symbolsolver.model.typesystem;

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.*;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration.Bound;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.*;
import com.github.javaparser.symbolsolver.AbstractSymbolResolutionTest;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.Serializable;
import java.net.ProtocolException;
import java.nio.Buffer;
import java.nio.CharBuffer;
import java.nio.file.FileSystemException;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.hamcrest.CoreMatchers.*;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.collection.IsIterableContainingInAnyOrder.containsInAnyOrder;
import static org.junit.jupiter.api.Assertions.*;

class ReferenceTypeTest extends AbstractSymbolResolutionTest {

    private ReferenceTypeImpl listOfA;
    private ReferenceTypeImpl listOfStrings;
    private ReferenceTypeImpl linkedListOfString;
    private ReferenceTypeImpl collectionOfString;
    private ReferenceTypeImpl listOfWildcardExtendsString;
    private ReferenceTypeImpl listOfWildcardSuperString;
    private ReferenceTypeImpl object;
    private ReferenceTypeImpl string;
    private TypeSolver typeSolver;
    private ReferenceTypeImpl ioException;
    private ResolvedType unionWithIOExceptionAsCommonAncestor;
    private ResolvedType unionWithThrowableAsCommonAncestor;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
        object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver));
        string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver));
        listOfA = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ResolvedTypeVariable(ResolvedTypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList()))));
        listOfStrings = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver))));
        linkedListOfString = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(LinkedList.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver))));
        collectionOfString = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(Collection.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver))));
        listOfWildcardExtendsString = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(ResolvedWildcard.extendsBound(string)));
        listOfWildcardSuperString = new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(ResolvedWildcard.superBound(string)));
        ioException = new ReferenceTypeImpl(new ReflectionClassDeclaration(IOException.class, typeSolver));
        unionWithIOExceptionAsCommonAncestor = new ResolvedUnionType(Arrays.asList(
                new ReferenceTypeImpl(new ReflectionClassDeclaration(ProtocolException.class, typeSolver)),
                new ReferenceTypeImpl(new ReflectionClassDeclaration(FileSystemException.class, typeSolver))
        ));
        unionWithThrowableAsCommonAncestor = new ResolvedUnionType(Arrays.asList(
                new ReferenceTypeImpl(new ReflectionClassDeclaration(ClassCastException.class, typeSolver)),
                new ReferenceTypeImpl(new ReflectionClassDeclaration(AssertionError.class, typeSolver))
        ));
        
        // minimal initialization of JavaParser
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        // Setup parser
        StaticJavaParser.setConfiguration(configuration);
    }

    @Test
    void testDerivationOfTypeParameters() {
        ReflectionTypeSolver typeSolver = new ReflectionTypeSolver();
        ReferenceTypeImpl ref1 = new ReferenceTypeImpl(typeSolver.solveType(LinkedList.class.getCanonicalName()));
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
    void testIsAssignableByBoxedPrimitive() {
        ResolvedReferenceType numberType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Number.class, typeSolver));
        ResolvedReferenceType intType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Integer.class, typeSolver));
        ResolvedReferenceType doubleType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Double.class, typeSolver));
        ResolvedReferenceType byteType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Byte.class, typeSolver));
        ResolvedReferenceType shortType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Short.class, typeSolver));
        ResolvedReferenceType charType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Character.class, typeSolver));
        ResolvedReferenceType longType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Long.class, typeSolver));
        ResolvedReferenceType booleanType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Boolean.class, typeSolver));
        ResolvedReferenceType floatType = new ReferenceTypeImpl(new ReflectionClassDeclaration(Float.class, typeSolver));

        assertEquals(true, numberType.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(true, numberType.isAssignableBy(ResolvedPrimitiveType.DOUBLE));
        assertEquals(true, numberType.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(true, numberType.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(true, numberType.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, numberType.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(true, intType.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(true, doubleType.isAssignableBy(ResolvedPrimitiveType.DOUBLE));
        assertEquals(true, byteType.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(true, shortType.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(true, charType.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(true, longType.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(true, booleanType.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(true, floatType.isAssignableBy(ResolvedPrimitiveType.FLOAT));
    }

    @Test
    void testIsCorresponding() {

        // ResolvedReferenceTypeTester is defined to allow to test protected method isCorrespondingBoxingType(..)
        class ResolvedReferenceTypeTester extends ReferenceTypeImpl {

            public ResolvedReferenceTypeTester(ResolvedReferenceTypeDeclaration typeDeclaration,
                                               TypeSolver typeSolver) {
                super(typeDeclaration);
            }

            public boolean isCorrespondingBoxingType(String name) {
                return super.isCorrespondingBoxingType(name);
            }

        }

        ResolvedReferenceTypeTester numberType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Number.class, typeSolver), typeSolver);
        ResolvedReferenceTypeTester intType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Integer.class, typeSolver), typeSolver);
        ResolvedReferenceTypeTester doubleType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Double.class, typeSolver), typeSolver);
        ResolvedReferenceTypeTester byteType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Byte.class, typeSolver), typeSolver);
        ResolvedReferenceTypeTester shortType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Short.class, typeSolver), typeSolver);
        ResolvedReferenceTypeTester charType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Character.class, typeSolver), typeSolver);
        ResolvedReferenceTypeTester longType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Long.class, typeSolver), typeSolver);
        ResolvedReferenceTypeTester booleanType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Boolean.class, typeSolver), typeSolver);
        ResolvedReferenceTypeTester floatType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(Float.class, typeSolver), typeSolver);

        ResolvedReferenceTypeTester otherType = new ResolvedReferenceTypeTester(
                new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);

        assertEquals(true, intType.isCorrespondingBoxingType(ResolvedPrimitiveType.INT.describe()));
        assertEquals(true, doubleType.isCorrespondingBoxingType(ResolvedPrimitiveType.DOUBLE.describe()));
        assertEquals(true, byteType.isCorrespondingBoxingType(ResolvedPrimitiveType.BYTE.describe()));
        assertEquals(true, shortType.isCorrespondingBoxingType(ResolvedPrimitiveType.SHORT.describe()));
        assertEquals(true, charType.isCorrespondingBoxingType(ResolvedPrimitiveType.CHAR.describe()));
        assertEquals(true, longType.isCorrespondingBoxingType(ResolvedPrimitiveType.LONG.describe()));
        assertEquals(true, booleanType.isCorrespondingBoxingType(ResolvedPrimitiveType.BOOLEAN.describe()));
        assertEquals(true, floatType.isCorrespondingBoxingType(ResolvedPrimitiveType.FLOAT.describe()));

        assertEquals(false, numberType.isCorrespondingBoxingType(ResolvedPrimitiveType.INT.describe()));

        assertThrows(IllegalArgumentException.class, () -> {
            intType.isCorrespondingBoxingType("String");
        });
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
    void testIsAssignableByUnionType() {
        assertEquals(true, ioException.isAssignableBy(unionWithIOExceptionAsCommonAncestor));
        assertEquals(false, ioException.isAssignableBy(unionWithThrowableAsCommonAncestor));
    }

    @Test
    void testGetAllAncestorsConsideringTypeParameters() {
        assertThat(linkedListOfString.getAllAncestors(), hasItem(object));
        assertThat(linkedListOfString.getAllAncestors(), hasItem(listOfStrings));
        assertThat(linkedListOfString.getAllAncestors(), hasItem(collectionOfString));
        assertThat(linkedListOfString.getAllAncestors(), not(hasItem(listOfA)));
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
        ReferenceTypeImpl foo = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver));
        ReferenceTypeImpl bar = new ReferenceTypeImpl(new ReflectionClassDeclaration(Bar.class, typeSolver));
        ReferenceTypeImpl left, right;

        //YES MoreBazzing<Foo, Bar> e1 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(foo, bar))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar)))
        );

        //YES MoreBazzing<? extends Foo, Bar> e2 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(ResolvedWildcard.extendsBound(foo), bar))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar)))
        );

        //YES MoreBazzing<Foo, ? extends Bar> e3 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(foo, ResolvedWildcard.extendsBound(bar)))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar)))
        );

        //YES MoreBazzing<? extends Foo, ? extends Foo> e4 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(ResolvedWildcard.extendsBound(foo), ResolvedWildcard.extendsBound(foo)))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar)))
        );

        //YES MoreBazzing<? extends Foo, ? extends Foo> e5 = new MoreBazzing<Bar, Bar>();
        left = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(ResolvedWildcard.extendsBound(foo), ResolvedWildcard.extendsBound(foo)));
        right = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(bar, bar));
        assertEquals(true, left.isAssignableBy(right));

        //YES Bazzer<Object, String, String> e6 = new MoreBazzing<String, Object>();
        left = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                ImmutableList.of(object, string, string));
        right = new ReferenceTypeImpl(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(string, object));

        // To debug the following
        List<ResolvedReferenceType> ancestors = right.getAllAncestors();
        ResolvedReferenceType moreBazzingAncestor = ancestors.stream()
                .filter(a -> a.getQualifiedName().endsWith("Bazzer"))
                .findFirst().get();

        assertEquals(true, left.isAssignableBy(right));

        //YES Bazzer<String,String,String> e7 = new MoreBazzing<String, String>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(string, string, string))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(string, string)))
        );

        //YES Bazzer<Bar,String,Foo> e8 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar, string, foo))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar)))
        );

        //YES Bazzer<Foo,String,Bar> e9 = new MoreBazzing<Bar, Foo>();
        assertEquals(true,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(foo, string, bar))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo)))
        );

        //NO Bazzer<Bar,String,Foo> n1 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar, string, foo))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo)))
        );

        //NO Bazzer<Bar,String,Bar> n2 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar, string, foo))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo)))
        );

        //NO Bazzer<Foo,Object,Bar> n3 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeImpl(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(foo, object, bar))
                        .isAssignableBy(new ReferenceTypeImpl(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo)))
        );
    }

    @Test
    void charSequenceIsAssignableToObject() {
        TypeSolver typeSolver = new ReflectionTypeSolver();
        ReferenceTypeImpl charSequence = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(CharSequence.class, typeSolver));
        ReferenceTypeImpl object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver));
        assertEquals(false, charSequence.isAssignableBy(object));
        assertEquals(true, object.isAssignableBy(charSequence));
    }

    @Test
    void testGetFieldTypeExisting() {
        class Foo<A> {

            List<A> elements;
        }

        TypeSolver typeSolver = new ReflectionTypeSolver();
        ReferenceTypeImpl ref = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver));

        assertEquals(true, ref.getFieldType("elements").isPresent());
        assertEquals(true, ref.getFieldType("elements").get().isReferenceType());
        assertEquals(List.class.getCanonicalName(), ref.getFieldType("elements").get().asReferenceType().getQualifiedName());
        assertEquals(1, ref.getFieldType("elements").get().asReferenceType().typeParametersValues().size());
        assertEquals(true, ref.getFieldType("elements").get().asReferenceType().typeParametersValues().get(0).isTypeVariable());
        assertEquals("A", ref.getFieldType("elements").get().asReferenceType().typeParametersValues().get(0).asTypeParameter().getName());

        ref = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver))));

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
        ReferenceTypeImpl ref = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver));

        assertEquals(false, ref.getFieldType("bar").isPresent());

        ref = new ReferenceTypeImpl(new ReflectionClassDeclaration(Foo.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver))));

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
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver));
        ResolvedReferenceType arrayListOfString = new ReferenceTypeImpl(arraylist, ImmutableList.of(string));
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
        ResolvedReferenceType rawArrayList = new ReferenceTypeImpl(arraylist);

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        rawArrayList.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(9, ancestors.size());

        ResolvedTypeVariable tv = new ResolvedTypeVariable(arraylist.getTypeParameters().get(0));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(RandomAccess.class, typeResolver)), ancestors.get("java.util.RandomAccess"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractCollection.class, typeResolver), ImmutableList.of(tv)), ancestors.get("java.util.AbstractCollection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeResolver), ImmutableList.of(tv)), ancestors.get("java.util.List"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Cloneable.class, typeResolver)), ancestors.get("java.lang.Cloneable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(tv)), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractList.class, typeResolver), ImmutableList.of(tv)), ancestors.get("java.util.AbstractList"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver)), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(tv)), ancestors.get("java.lang.Iterable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Serializable.class, typeResolver)), ancestors.get("java.io.Serializable"));
    }

    @Test
    void testGetAllAncestorsOnTypeWithSpecifiedTypeParametersForInterface() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedInterfaceDeclaration list = new ReflectionInterfaceDeclaration(List.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver));
        ResolvedReferenceType listOfString = new ReferenceTypeImpl(list, ImmutableList.of(string));

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        listOfString.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(2, ancestors.size());

        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.lang.Iterable"));
    }

    @Test
    void testGetAllAncestorsOnTypeWithSpecifiedTypeParametersForClassAbstractCollection() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration abstractCollection = new ReflectionClassDeclaration(AbstractCollection.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver));
        ResolvedReferenceType abstractCollectionOfString = new ReferenceTypeImpl(abstractCollection, ImmutableList.of(string));

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        abstractCollectionOfString.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(3, ancestors.size());

        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver)), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.lang.Iterable"));
    }

    @Test
    void testGetAllAncestorsOnTypeWithSpecifiedTypeParametersForClassAbstractList() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration abstractList = new ReflectionClassDeclaration(AbstractList.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver));
        ResolvedReferenceType abstractListOfString = new ReferenceTypeImpl(abstractList, ImmutableList.of(string));

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        abstractListOfString.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(5, ancestors.size());

        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractCollection.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.AbstractCollection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.List"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver)), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.lang.Iterable"));
    }

    @Test
    void testGetAllAncestorsOnTypeWithSpecifiedTypeParametersForClassArrayList() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedClassDeclaration arraylist = new ReflectionClassDeclaration(ArrayList.class, typeResolver);
        ResolvedType string = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver));
        ResolvedReferenceType arrayListOfString = new ReferenceTypeImpl(arraylist, ImmutableList.of(string));

        Map<String, ResolvedReferenceType> ancestors = new HashMap<>();
        arrayListOfString.getAllAncestors().forEach(a -> ancestors.put(a.getQualifiedName(), a));
        assertEquals(9, ancestors.size());

        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(RandomAccess.class, typeResolver)), ancestors.get("java.util.RandomAccess"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractCollection.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.AbstractCollection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(List.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.List"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Cloneable.class, typeResolver)), ancestors.get("java.lang.Cloneable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Collection.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.Collection"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(AbstractList.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.util.AbstractList"));
        assertEquals(new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeResolver)), ancestors.get("java.lang.Object"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Iterable.class, typeResolver), ImmutableList.of(string)), ancestors.get("java.lang.Iterable"));
        assertEquals(new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Serializable.class, typeResolver)), ancestors.get("java.io.Serializable"));
    }

    @Test
    void testTypeParametersValues() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedReferenceType stream = new ReferenceTypeImpl(new ReflectionInterfaceDeclaration(Stream.class, typeResolver));
        assertEquals(1, stream.typeParametersValues().size());
        assertEquals(new ResolvedTypeVariable(new ReflectionInterfaceDeclaration(Stream.class, typeResolver).getTypeParameters().get(0)), stream.typeParametersValues().get(0));
    }

    @Test
    void testReplaceTypeVariables() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedInterfaceDeclaration streamInterface = new ReflectionInterfaceDeclaration(Stream.class, typeResolver);
        ResolvedReferenceType stream = new ReferenceTypeImpl(streamInterface);

        ResolvedMethodDeclaration streamMap = streamInterface.getDeclaredMethods().stream().filter(m -> m.getName().equals("map")).findFirst().get();
        ResolvedTypeParameterDeclaration streamMapR = streamMap.findTypeParameter("T").get();
        ResolvedTypeVariable typeVariable = new ResolvedTypeVariable(streamMapR);
        stream = stream.deriveTypeParameters(stream.typeParametersMap().toBuilder().setValue(stream.getTypeDeclaration().get().getTypeParameters().get(0), typeVariable).build());

        ResolvedTypeParameterDeclaration tpToReplace = streamInterface.getTypeParameters().get(0);
        ResolvedType replaced = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver));

        ResolvedType streamReplaced = stream.replaceTypeVariables(tpToReplace, replaced);
        assertEquals("java.util.stream.Stream<java.lang.String>", streamReplaced.describe());
    }

    @Test
    void testReplaceTypeVariablesWithLambdaInBetween() {
        TypeSolver typeResolver = new ReflectionTypeSolver();
        ResolvedInterfaceDeclaration streamInterface = new ReflectionInterfaceDeclaration(Stream.class, typeResolver);
        ResolvedReferenceType stream = new ReferenceTypeImpl(streamInterface);

        ResolvedMethodDeclaration streamMap = streamInterface.getDeclaredMethods().stream().filter(m -> m.getName().equals("map")).findFirst().get();
        ResolvedTypeParameterDeclaration streamMapR = streamMap.findTypeParameter("T").get();
        ResolvedTypeVariable typeVariable = new ResolvedTypeVariable(streamMapR);
        stream = stream.deriveTypeParameters(stream.typeParametersMap().toBuilder().setValue(stream.getTypeDeclaration().get().getTypeParameters().get(0), typeVariable).build());

        ResolvedTypeParameterDeclaration tpToReplace = streamInterface.getTypeParameters().get(0);
        ResolvedType replaced = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeResolver));

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
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver))));
        assertEquals(0, iterableOfString.getDirectAncestors().size());
    }

    @Test
    void testDirectAncestorsOfInterfaceExtendingInterface() {
        assertEquals(1, collectionOfString.getDirectAncestors().size());
        ResolvedReferenceType ancestor1 = collectionOfString.getDirectAncestors().get(0);
        assertEquals("java.lang.Iterable", ancestor1.getQualifiedName());
        assertEquals(1, ancestor1.getTypeParametersMap().size());
        assertEquals("T", ancestor1.getTypeParametersMap().get(0).a.getName());
        assertEquals("java.lang.String", ancestor1.getTypeParametersMap().get(0).b.describe());
    }

    @Test
    void testDirectAncestorsOfClassWithoutSuperClassOrInterfaces() {
        ResolvedReferenceType buffer = new ReferenceTypeImpl(new ReflectionClassDeclaration(Buffer.class, typeSolver));
        Set<String> ancestors = buffer.getDirectAncestors()
                .stream()
                .map(ResolvedReferenceType::describe)
                .collect(Collectors.toSet());

        assertThat(ancestors, equalTo(new HashSet<>(Arrays.asList("java.lang.Object"))));
    }

    @Test
    void testDirectAncestorsOfObjectClass() {
        ResolvedReferenceType object = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver));
        Set<String> ancestors = object.getDirectAncestors()
                .stream()
                .map(ResolvedReferenceType::describe)
                .collect(Collectors.toSet());

        assertEquals(new HashSet<>(), ancestors);
    }

    @Test
    void testDirectAncestorsOfClassWithSuperClass() {
        ResolvedReferenceType charbuffer = new ReferenceTypeImpl(new ReflectionClassDeclaration(CharBuffer.class, typeSolver));
        Set<String> ancestors = charbuffer.getDirectAncestors()
                .stream()
                .map(ResolvedReferenceType::describe)
                .collect(Collectors.toSet());

        assertThat(ancestors, containsInAnyOrder(
                "java.lang.CharSequence",
                "java.lang.Appendable",
                "java.nio.Buffer",
                "java.lang.Readable",
                "java.lang.Comparable<java.nio.CharBuffer>"
        ));
    }

    @Test
    void testDirectAncestorsOfClassWithInterfaces() {
        Set<String> ancestors = string.getDirectAncestors()
                .stream()
                .map(ResolvedReferenceType::describe)
                .collect(Collectors.toSet());

        // FIXME: Remove this temporary fix which varies the test based on the detected JDK which is running these tests.
        TestJdk currentJdk = TestJdk.getCurrentHostJdk();
        if (currentJdk.getMajorVersion() < 12) {
            // JDK 12 introduced "java.lang.constant.Constable"
            assertThat(ancestors, containsInAnyOrder(
                    "java.lang.CharSequence",
                    "java.lang.Object",
                    "java.lang.Comparable<java.lang.String>",
                    "java.io.Serializable"
            ));
        } else {
            // JDK 12 introduced "java.lang.constant.Constable"
            assertThat(ancestors, containsInAnyOrder(
                    "java.lang.CharSequence",
                    "java.lang.Object",
                    "java.lang.Comparable<java.lang.String>",
                    "java.io.Serializable",
                    "java.lang.constant.Constable",
                    "java.lang.constant.ConstantDesc"
            ));
        }
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

        ResolvedReferenceType rtA = new ReferenceTypeImpl(classA.resolve());
        ResolvedReferenceType rtB = new ReferenceTypeImpl(classB.resolve());

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

        ResolvedReferenceType rtA = new ReferenceTypeImpl(classA.resolve());
        ResolvedReferenceType rtB = new ReferenceTypeImpl(classB.resolve());

        assertEquals(2, rtA.getAllFieldsVisibleToInheritors().size());
        assertTrue(rtA.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("c")));
        assertTrue(rtA.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("l")));

        assertEquals(3, rtB.getAllFieldsVisibleToInheritors().size());
        assertTrue(rtB.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("c")));
        assertTrue(rtB.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("l")));
        assertTrue(rtB.getAllFieldsVisibleToInheritors().stream().anyMatch(f -> f.getName().equals("b")));
    }
    
    @Test
    void erasure_non_generic_type() {
        List<ResolvedType> types = declaredTypes(
                "class A {}");
        ResolvedType expected = types.get(0);
        assertEquals(expected, types.get(0).erasure());
    }
    
    @Test
    // The erasure of a parameterized type
    void erasure_rawtype() {
        List<ResolvedType> types = declaredTypes(
                "class A<String> {}");
        ResolvedType rt = types.get(0);
        String expected = "A";
        ResolvedType erasedType = rt.erasure();
        assertTrue(rt.asReferenceType().isRawType());
        assertTrue(erasedType.asReferenceType().typeParametersValues().isEmpty());
        assertEquals(expected, erasedType.describe());
    }

    @Test
    // The erasure of an array type T[] is |T|[].
    void erasure_arraytype() {
        // create a type : List <String>
        ResolvedType genericList = array(genericType(List.class.getCanonicalName(), String.class.getCanonicalName()));
        String expected = "java.util.List[]";
        assertEquals(expected, genericList.erasure().describe());
    }
    
    @Test
    // The erasure of an array type T[] is |T|[].
    void erasure_arraytype_with_bound() {
        // create a type : List <T extends Serializable>
        ResolvedTypeVariable typeArguments = parametrizedType("T", Serializable.class.getCanonicalName());
        ResolvedType genericList = array(genericType(List.class.getCanonicalName(), typeArguments));
        String expected = "java.util.List<java.io.Serializable>[]";
        assertEquals(expected, genericList.erasure().describe());
    }
    
    @Test
    // The erasure of a type variable (§4.4) is the erasure of its leftmost bound.
    void erasure_type_variable() {
        List<ResolvedType> types = declaredTypes(
                "class A<T extends Number> {}");
        ResolvedType rt = types.get(0);
        String expected =  "A<java.lang.Number>";
        assertEquals(expected, rt.erasure().describe());
    }
    
    @Test
    // The erasure of a nested type T.C is |T|.C.
    void erasure_nested_type() {
        List<ResolvedType> types = declaredTypes(
                "class A<T> {" +
                        "  class C{}" +
                        "}",
                "class A {" +
                        "  class C{}" +
                        "}");
        ResolvedType typeA = types.get(0);
        ResolvedType typeC = types.get(1);
        // ResolvedType expectedErasedAType= types.get(2);
        ResolvedType expectedErasedCType = types.get(3);
        String expectedA = "A";
        String expectedC = "A.C";
        assertEquals(expectedA, typeA.erasure().describe());
        assertEquals(expectedC, typeC.erasure().describe());
        // this type declaration are not equals because the type returned by typeA.erasure() always contains original
        // typeParameters
        // assertEquals(expectedErasedAType, typeA.erasure());
        assertEquals(expectedErasedCType, typeC.erasure());
    }
    
    // return a generic type with type arguments (arguments can be bounded)
    private ResolvedType genericType(String type, ResolvedType... parameterTypes) {
        return type(type, toList(parameterTypes));
    }
    
    // return a generic type with type arguments
    private ResolvedType genericType(String type, String... parameterTypes) {
        return new ReferenceTypeImpl(typeSolver.solveType(type), types(parameterTypes));
    }
    
    // return a list of types
    private List<ResolvedType> types(String... types) {
        return Arrays.stream(types).map(type -> type(type)).collect(Collectors.toList());
    }

    // return the specified type
    private ResolvedType type(String type) {
        return type(type, new ArrayList<>());
    }
    
    private ResolvedType type(String type, List<ResolvedType> typeArguments) {
        return new ReferenceTypeImpl(typeSolver.solveType(type), typeArguments);
    }
    
    // return a type parameter
    private ResolvedTypeVariable parametrizedType(String type, String parameterType) {
        return new ResolvedTypeVariable(ResolvedTypeParameterDeclaration.onType(parameterType, type + "." + parameterType,
                Arrays.asList((extendBound(parameterType)))));
    }

    // rturn an extend bound
    private Bound extendBound(String type) {
        return Bound.extendsBound(type(type));
    }

    private Set<ResolvedType> toSet(ResolvedType... resolvedTypes) {
        return new HashSet<>(toList(resolvedTypes));
    }
    
    private List<ResolvedType> toList(ResolvedType... resolvedTypes) {
        return Arrays.asList(resolvedTypes);
    }
    
    // return an array type from the base type
    private ResolvedType array(ResolvedType baseType) {
        return new ResolvedArrayType(baseType);
    }
    
    // return a list of types from the declared types (using a static parser) 
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
