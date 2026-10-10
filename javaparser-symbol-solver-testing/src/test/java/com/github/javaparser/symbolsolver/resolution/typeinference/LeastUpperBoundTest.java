/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.typesystem.LazyType;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedIntersectionType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedWildcard;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.Lists;
import java.io.FileNotFoundException;
import java.io.IOError;
import java.io.IOException;
import java.io.Serializable;
import java.net.URISyntaxException;
import java.util.*;
import java.util.stream.Collectors;
import org.junit.jupiter.api.*;

class LeastUpperBoundTest {

    private TypeSolver typeSolver;

    // Each test class owns its own parser/config instead of mutating the shared
    // StaticJavaParser state, so it doesn't depend on (or leak into) global config.
    private static final JavaParserAdapter parser = JavaParserAdapter.of(new JavaParser(
            new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()))));

    @AfterAll
    static void tearDownAfterClass() throws Exception {}

    @BeforeEach
    void setUp() throws Exception {
        typeSolver = new ReflectionTypeSolver();
    }

    @AfterEach
    void tearDown() throws Exception {}

    @Test
    public void lub_of_one_element_is_itself() {
        ResolvedType exception = type(Exception.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(exception);
        assertEquals(lub, exception);
    }

    @Test
    void lub_of_one_lazy_type_is_its_concrete_type() {
        ResolvedType exception = type(Exception.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(new LazyType(v -> exception));
        assertEquals(exception, lub);
    }

    @Test
    public void lub_of_one_null_element_is_itself() {
        ResolvedType lub = leastUpperBound(NullType.INSTANCE);
        assertEquals(lub, lub);
    }

    @Test
    public void lub_should_fail_if_no_type_provided() {
        try {
            ResolvedType lub = leastUpperBound(new ResolvedType[] {});
            fail("should have failed");
        } catch (Exception e) {
            assertTrue(e instanceof IllegalArgumentException);
        }
    }

    @Test
    public void lub_with_shared_supertypes() {
        ResolvedType exception = type(Exception.class.getCanonicalName());
        ResolvedType error = type(Error.class.getCanonicalName());
        ResolvedType expected = type(Throwable.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(exception, error);
        assertEquals(expected, lub);
    }

    @Test
    public void lub_with_shared_supertypes_from_interface() {
        ResolvedType exception = type(Exception.class.getCanonicalName());
        ResolvedType throwable = type(Throwable.class.getCanonicalName());
        ResolvedType serializable = type(Serializable.class.getCanonicalName());
        ResolvedType expected = type(Serializable.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(exception, throwable, serializable);
        assertEquals(expected, lub);
    }

    @Test
    public void lub_with_shared_supertypes_from_serializable() {
        ResolvedType exception = type(Exception.class.getCanonicalName());
        ResolvedType string = type(String.class.getCanonicalName());
        ResolvedType expected = type(Serializable.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(exception, string);
        assertEquals(expected, lub);
    }

    @Test
    public void lub_with_hierarchy_of_supertypes1() {
        ResolvedType exception = type(Exception.class.getCanonicalName());
        ResolvedType ioexception = type(IOException.class.getCanonicalName());
        ResolvedType expected = type(Exception.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(exception, ioexception);
        assertEquals(expected, lub);
    }

    @Test
    public void lub_with_hierarchy_of_supertypes2() {
        ResolvedType error = type(Error.class.getCanonicalName());
        ResolvedType ioexception = type(IOException.class.getCanonicalName());
        ResolvedType ioerror = type(IOError.class.getCanonicalName());
        ResolvedType expected = type(Throwable.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(error, ioexception, ioerror);
        assertEquals(expected, lub);
    }

    @Test
    public void lub_with_no_shared_supertypes_exception_object() {
        List<ResolvedType> types = declaredTypes("class A extends Exception {}", "class B {}");
        ResolvedType a = types.get(0);
        ResolvedType b = types.get(1);
        ResolvedType lub = leastUpperBound(a, b);
        ResolvedType expected = type("java.lang.Object");
        assertEquals(expected, lub);
    }

    @Test
    public void lub_approximation_inheritance_and_multiple_bounds() {
        List<ResolvedType> types = declaredTypes(
                "class A implements I1, I2 {}", "class B implements I2, I1 {}", "interface I1 {}", "interface I2 {}");
        ResolvedType a = types.get(0);
        ResolvedType b = types.get(1);
        ResolvedType lub = leastUpperBound(a, b);
        ResolvedType expected = types.get(2);
        // should be <I1 & I2>, not only I1 (first interface of first type analyzed)
        assertEquals(expected, lub);
    }

    @Test
    public void lub_approximation_with_complexe_inheritance() {
        ResolvedType expected = type(Exception.class.getCanonicalName());
        // java.lang.Object/java.lang.Throwable/java.lang.Exception/java.net.URISyntaxException
        ResolvedType uriSyntaxException = type(URISyntaxException.class.getCanonicalName());
        // java.lang.Object//java.lang.Throwable/java.lang.Exception/java.io.IOException/java.io.FileNotFoundException
        ResolvedType fileNotFoundException = type(FileNotFoundException.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(uriSyntaxException, fileNotFoundException);
        assertEquals(expected, lub);
    }

    @Test
    public void lub_with_unknown_inheritance() {
        List<ResolvedType> types = declaredTypes("class A extends Exception {}", "class B extends UnknownException {}");
        ResolvedType a = types.get(0);
        ResolvedType b = types.get(1);
        try {
            ResolvedType lub = leastUpperBound(a, b);
            fail("UnknownException cannot be resolved");
        } catch (UnsolvedSymbolException e) {
            assertTrue(e instanceof UnsolvedSymbolException);
        }
    }

    @Test
    public void lub_of_null_and_object() {
        ResolvedType nullType = NullType.INSTANCE;
        ResolvedType stringType = type(String.class.getCanonicalName());
        ResolvedType expected = type(String.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(nullType, stringType);
        assertEquals(expected, lub);
    }

    @Test
    void lub_of_interface_and_class_not_implementing_it_is_object() {
        // Object is a supertype of every interface (JLS 4.10.2), see issue #5158
        ResolvedType map = genericType(
                Map.class.getCanonicalName(), String.class.getCanonicalName(), String.class.getCanonicalName());
        ResolvedType integer = type(Integer.class.getCanonicalName());
        assertEquals(type(Object.class.getCanonicalName()), leastUpperBound(map, integer));
    }

    @Test
    void lub_of_declared_interface_and_class_not_implementing_it_is_object() {
        ResolvedType i1 = declaredTypes("interface I1 {}").get(0);
        ResolvedType integer = type(Integer.class.getCanonicalName());
        assertEquals(type(Object.class.getCanonicalName()), leastUpperBound(i1, integer));
    }

    @Test
    void lub_of_unrelated_interfaces_is_object() {
        ResolvedType map = genericType(
                Map.class.getCanonicalName(), String.class.getCanonicalName(), String.class.getCanonicalName());
        ResolvedType runnable = type(Runnable.class.getCanonicalName());
        assertEquals(type(Object.class.getCanonicalName()), leastUpperBound(map, runnable));
    }

    @Test
    void lub_of_interface_and_class_sharing_an_interface() {
        // non-regression: Object must not hide the shared interface
        ResolvedType arrayList = genericType(ArrayList.class.getCanonicalName(), String.class.getCanonicalName());
        ResolvedType integer = type(Integer.class.getCanonicalName());
        assertEquals(type(Serializable.class.getCanonicalName()), leastUpperBound(arrayList, integer));
    }

    @Test
    void lub_of_interface_and_class_without_type_solver_is_null() {
        // without a type solver, Object cannot be added to the supertypes of interfaces
        ResolvedType runnable = type(Runnable.class.getCanonicalName());
        ResolvedType integer = type(Integer.class.getCanonicalName());
        assertNull(TypeHelper.leastUpperBound(toSet(runnable, integer)));
    }

    @Test
    public void lub_of_enum() {
        ResolvedType type = type("java.math.RoundingMode");

        ResolvedReferenceTypeDeclaration typeDeclaration =
                type.asReferenceType().getTypeDeclaration().get();

        List<ResolvedType> constanteTypes = typeDeclaration.asEnum().getEnumConstants().stream()
                .map(enumConst -> enumConst.getType())
                .collect(Collectors.toList());

        ResolvedType expected = constanteTypes.get(0);

        ResolvedType lub = leastUpperBound(constanteTypes.get(0), constanteTypes.get(1));
        assertEquals(
                expected.asReferenceType().describe(), lub.asReferenceType().describe());
    }

    @Test
    public void lub_of_generics_with_shared_super_class() {
        List<ResolvedType> types = declaredTypes(
                "class A extends Exception {}",
                "class B extends Exception implements I1<Exception> {}",
                "interface I1<T> {}");
        ResolvedType expected = type(Exception.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(types.get(0), types.get(1));
        assertEquals(expected, lub);
    }

    @Test
    public void lub_of_generics_with_inheritance() {
        List<ResolvedType> types =
                declaredTypes("class A<T> extends java.util.List<T> {}", "class B extends A<String> {}");
        ResolvedType expected = types.get(0);
        ResolvedType lub = leastUpperBound(types.get(0), types.get(1));
        ResolvedType erased = lub.erasure();
        assertEquals(expected.erasure(), erased);
        assertTrue(!lub.asReferenceType().typeParametersValues().isEmpty());
    }

    @Test
    void lub_of_generics_with_different_parametrized_type() {
        ResolvedType list1 = genericType(List.class.getCanonicalName(), String.class.getCanonicalName());
        ResolvedType list2 = genericType(List.class.getCanonicalName(), Object.class.getCanonicalName());
        // lcta(String, Object) = ? extends Object = ?, List<Object> is not a supertype of List<String>
        ResolvedType expected = genericType(List.class.getCanonicalName(), unbound());
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected, lub);
    }

    @Test
    void lub_of_generics_with_different_parametrized_type2() {
        ResolvedType list1 = genericType(HashSet.class.getCanonicalName(), String.class.getCanonicalName());
        ResolvedType list2 = genericType(LinkedHashSet.class.getCanonicalName(), String.class.getCanonicalName());
        ResolvedType expected = genericType(HashSet.class.getCanonicalName(), String.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected, lub);
    }

    @Test
    void lub_of_generics_with_different_bound_on_same_type() {
        ResolvedType list1 =
                genericType(List.class.getCanonicalName(), extendsBound(Exception.class.getCanonicalName()));
        ResolvedType list2 = genericType(List.class.getCanonicalName(), superBound(Exception.class.getCanonicalName()));
        // lcta(? extends U, ? super V) = ?, List<Exception> is not a supertype of List<? extends Exception>
        ResolvedType expected = genericType(List.class.getCanonicalName(), unbound());
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    void lub_of_generics_with_bounded_type_in_hierarchy() {
        ResolvedType list1 = genericType(List.class.getCanonicalName(), Number.class.getCanonicalName());
        ResolvedType list2 = genericType(List.class.getCanonicalName(), Integer.class.getCanonicalName());
        ResolvedType expected =
                genericType(List.class.getCanonicalName(), extendsBound(Number.class.getCanonicalName()));
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    void lub_of_generics_with_type_and_extends_wildcard() {
        ResolvedType list1 = genericType(List.class.getCanonicalName(), Integer.class.getCanonicalName());
        ResolvedType list2 = genericType(List.class.getCanonicalName(), extendsBound(Long.class.getCanonicalName()));
        // lcta(U, ? extends V) = ? extends lub(U, V)
        ResolvedType expected =
                genericType(List.class.getCanonicalName(), extendsBound(Number.class.getCanonicalName()));
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    void lub_of_generics_with_type_and_super_wildcard() {
        ResolvedType list1 = genericType(List.class.getCanonicalName(), Integer.class.getCanonicalName());
        ResolvedType list2 = genericType(List.class.getCanonicalName(), superBound(Integer.class.getCanonicalName()));
        // lcta(U, ? super V) = ? super glb(U, V)
        ResolvedType expected =
                genericType(List.class.getCanonicalName(), superBound(Integer.class.getCanonicalName()));
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    void lub_of_generics_with_two_super_wildcards() {
        ResolvedType integer = type(Integer.class.getCanonicalName());
        ResolvedType lng = type(Long.class.getCanonicalName());
        ResolvedType list1 = genericType(List.class.getCanonicalName(), superBound(Integer.class.getCanonicalName()));
        ResolvedType list2 = genericType(List.class.getCanonicalName(), superBound(Long.class.getCanonicalName()));
        // lcta(? super U, ? super V) = ? super glb(U, V)
        ResolvedType lub = leastUpperBound(list1, list2);
        ResolvedType typeArgument = lub.asReferenceType().typeParametersValues().get(0);
        assertTrue(typeArgument.isWildcard() && typeArgument.asWildcard().isSuper());
        ResolvedType glb = typeArgument.asWildcard().getBoundedType();
        assertTrue(glb instanceof ResolvedIntersectionType);
        assertEquals(toSet(integer, lng), new HashSet<>(((ResolvedIntersectionType) glb).getElements()));
    }

    @Test
    void lub_of_generics_with_unbounded_wildcard() {
        ResolvedType unboundedList = genericType(List.class.getCanonicalName(), unbound());
        ResolvedType[] lists = {
            genericType(List.class.getCanonicalName(), String.class.getCanonicalName()),
            genericType(List.class.getCanonicalName(), extendsBound(Integer.class.getCanonicalName())),
            genericType(List.class.getCanonicalName(), superBound(Integer.class.getCanonicalName()))
        };
        for (ResolvedType list : lists) {
            assertEquals(unboundedList, leastUpperBound(list, unboundedList), list.describe());
        }
    }

    @Test
    void lub_of_generics_computes_same_type_arguments_consistently() {
        String list = List.class.getCanonicalName();
        ResolvedType listOfString = genericType(list, String.class.getCanonicalName());
        ResolvedType listOfInteger = genericType(list, Integer.class.getCanonicalName());
        ResolvedType map1 = genericType(Map.class.getCanonicalName(), listOfString, listOfString);
        ResolvedType map2 = genericType(Map.class.getCanonicalName(), listOfInteger, listOfInteger);
        // both type arguments are computed from the same lcta, so they must be equal
        ResolvedType lub = leastUpperBound(map1, map2);
        List<ResolvedType> typeArguments = lub.asReferenceType().typeParametersValues();
        assertEquals(
                "? extends java.util.List<? extends java.io.Serializable>",
                typeArguments.get(0).describe());
        assertEquals(typeArguments.get(0), typeArguments.get(1));
    }

    @Test
    void lub_of_generics_with_upper_bounded_type_in_hierarchy() {
        ResolvedType list1 = genericType(List.class.getCanonicalName(), extendsBound(Number.class.getCanonicalName()));
        ResolvedType list2 = genericType(List.class.getCanonicalName(), extendsBound(Integer.class.getCanonicalName()));
        ResolvedType expected =
                genericType(List.class.getCanonicalName(), extendsBound(Number.class.getCanonicalName()));
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    void lub_of_generics_with_type_variable_of_a_type() {
        ResolvedType listOfT = declaredFieldType("class A<T> { java.util.List<T> f; }");
        ResolvedType listOfString = genericType(List.class.getCanonicalName(), String.class.getCanonicalName());
        // T is a type: lcta(String, T) = ? extends lub(String, T) = ?
        ResolvedType expected = genericType(List.class.getCanonicalName(), unbound());
        ResolvedType lub = leastUpperBound(listOfString, listOfT);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    void lub_of_generics_with_type_variable_of_a_method() {
        ResolvedType listOfT = declaredMethodReturnType("class A { <T> java.util.List<T> m() { return null; } }");
        ResolvedType listOfString = genericType(List.class.getCanonicalName(), String.class.getCanonicalName());
        // a type variable of a method is a type argument that was not inferred, it is replaced by the other one
        ResolvedType lub = leastUpperBound(listOfString, listOfT);
        assertEquals(listOfString.describe(), lub.describe());
    }

    @Test
    void lub_of_arrays_of_reference_types_is_an_array() {
        ResolvedType strings = new ResolvedArrayType(type(String.class.getCanonicalName()));
        ResolvedType integers = new ResolvedArrayType(type(Integer.class.getCanonicalName()));
        // S[] is a direct supertype of T[] when S is a direct supertype of T (JLS 4.10.3)
        assertEquals(
                new ResolvedArrayType(type(Serializable.class.getCanonicalName())), leastUpperBound(strings, integers));
    }

    @Test
    void lub_of_arrays_of_parameterized_types_keeps_type_arguments() {
        ResolvedType listsOfString =
                new ResolvedArrayType(genericType(List.class.getCanonicalName(), String.class.getCanonicalName()));
        ResolvedType listsOfInteger =
                new ResolvedArrayType(genericType(List.class.getCanonicalName(), Integer.class.getCanonicalName()));
        assertEquals(
                "java.util.List<? extends java.io.Serializable>[]",
                leastUpperBound(listsOfString, listsOfInteger).describe());
    }

    @Test
    void lub_of_multidimensional_array_and_array() {
        ResolvedType stringMatrix = new ResolvedArrayType(new ResolvedArrayType(type(String.class.getCanonicalName())));
        ResolvedType integers = new ResolvedArrayType(type(Integer.class.getCanonicalName()));
        // lub(String[], Integer)[]: an array is Serializable
        assertEquals(
                new ResolvedArrayType(type(Serializable.class.getCanonicalName())),
                leastUpperBound(stringMatrix, integers));
    }

    @Test
    void lub_of_arrays_of_primitive_and_reference_types() {
        ResolvedType ints = new ResolvedArrayType(ResolvedPrimitiveType.INT);
        ResolvedType strings = new ResolvedArrayType(type(String.class.getCanonicalName()));
        // Object, Cloneable and Serializable are the supertypes of every array type (JLS 4.10.3): the lub is
        // Cloneable & Serializable, approximated by its first interface in the order of their qualified names
        assertEquals(type(Serializable.class.getCanonicalName()), leastUpperBound(ints, strings));
        assertEquals(
                type(Serializable.class.getCanonicalName()),
                leastUpperBound(ints, new ResolvedArrayType(ResolvedPrimitiveType.LONG)));
    }

    @Test
    void lub_of_array_and_class() {
        ResolvedType strings = new ResolvedArrayType(type(String.class.getCanonicalName()));
        assertEquals(
                type(Serializable.class.getCanonicalName()),
                leastUpperBound(strings, type(Integer.class.getCanonicalName())));
        assertEquals(
                type(Object.class.getCanonicalName()), leastUpperBound(strings, type(Thread.class.getCanonicalName())));
    }

    @Test
    void lub_of_type_variable_and_class() {
        List<ResolvedType> types =
                declaredMethodParameterTypes("class A { <T extends Number> void m(T t, Integer i) {} }");
        // the supertypes of T are those of its bound
        ResolvedType lub = leastUpperBound(types.get(0), types.get(1));
        assertEquals(type(Number.class.getCanonicalName()), lub);
    }

    @Test
    void lub_of_type_variable_with_parameterized_bound() {
        List<ResolvedType> types = declaredMethodParameterTypes(
                "class A { <T extends java.util.List<String>> void m(T t, java.util.ArrayList<Integer> l) {} }");
        // the type arguments of the bound of T are kept
        ResolvedType lub = leastUpperBound(types.get(0), types.get(1));
        assertEquals("java.util.List<? extends java.io.Serializable>", lub.describe());
    }

    @Test
    void lub_of_type_variable_with_several_bounds() {
        List<ResolvedType> types = declaredMethodParameterTypes(
                "class A { <T extends Runnable & Comparable<T>> void m(T t, String s) {} }");
        // Comparable is a supertype of T through its second bound
        ResolvedType lub = leastUpperBound(types.get(0), types.get(1));
        assertEquals(type(Comparable.class.getCanonicalName()).erasure(), lub.erasure());
    }

    @Test
    void lub_of_generics_with_bounded_type_variable() {
        ResolvedType listOfT = declaredFieldType("class A<T extends Number> { java.util.List<T> f; }");
        ResolvedType listOfString = genericType(List.class.getCanonicalName(), String.class.getCanonicalName());
        // a bounded type variable cannot be replaced by String: lcta(String, T) = ? extends lub(String, Number)
        ResolvedType expected =
                genericType(List.class.getCanonicalName(), extendsBound(Serializable.class.getCanonicalName()));
        ResolvedType lub = leastUpperBound(listOfString, listOfT);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    public void lub_of_generics_with_raw_type() {
        List<ResolvedType> types = declaredTypes(
                "class Parent<X> {}",
                "class Child<Y> extends Parent<Y> {}",
                "class ChildString extends Child<String> {}",
                "class ChildRaw extends Child {}");
        ResolvedType ChildString = types.get(2);
        ResolvedType ChildRaw = types.get(3);

        ResolvedType lub = leastUpperBound(ChildString, ChildRaw);
        // the supertypes of the raw type Child are raw (JLS 4.8), and the raw type Child is a supertype of
        // Child<String>
        ResolvedType expected = types.get(1).erasure();
        assertEquals(expected, lub);
        assertTrue(lub.asReferenceType().isRawType());
    }

    @Test
    void lub_of_generics_with_supertype_inherited_through_a_raw_type() {
        List<ResolvedType> types = declaredTypes(
                "class Parent<X> {}",
                "class Child<Y> extends Parent<Y> {}",
                "class ParentString extends Parent<String> {}",
                "class ChildRaw extends Child {}");
        ResolvedType parentString = types.get(2);
        ResolvedType childRaw = types.get(3);

        // Parent is inherited through the raw type Child, so it is raw too (JLS 4.8)
        ResolvedType lub = leastUpperBound(parentString, childRaw);
        assertEquals(types.get(0).erasure(), lub);
    }

    @Test
    void lub_of_generics_keeps_type_variables_of_enclosing_types() {
        CompilationUnit cu = treeOf(
                "class Outer<T> {",
                "  class Inner1 extends java.util.ArrayList<T> {}",
                "  class Inner2 extends java.util.ArrayList<T> {}",
                "}");
        List<ResolvedType> inners = cu.findAll(ClassOrInterfaceDeclaration.class).stream()
                .filter(c -> c.getNameAsString().startsWith("Inner"))
                .map(c -> (ResolvedType) new ReferenceTypeImpl(c.resolve()))
                .collect(Collectors.toList());

        // T is in the scope of the inner classes: ArrayList<T> is not inherited through a raw type
        ResolvedType lub = leastUpperBound(inners.get(0), inners.get(1));
        assertEquals("java.util.ArrayList<T>", lub.describe());
    }

    @Test
    public void lub_of_generics_with_inheritance_and_wildcard() {
        List<ResolvedType> types = declaredTypes(
                "class Parent<X> {}",
                "class Child<Y> extends Parent<Y> {}",
                "class Other<Z> {}",
                "class A {}",
                "class ChildP extends Parent<Other<? extends A>> {}",
                "class ChildC extends Child<Other<? extends A>> {}");
        ResolvedType ChildP = types.get(4);
        ResolvedType childC = types.get(5);

        // lcta(U, U) = U, the type arguments of ancestors declared in source code being lazy types
        ResolvedType lub = leastUpperBound(ChildP, childC);
        assertEquals("Parent<Other<? extends A>>", lub.describe());
    }

    @Test
    public void lub_of_generics_without_loop() {
        List<ResolvedType> types = declaredTypes(
                "class Parent<X1, X2> {}",
                "class Child<Y1, Y2> extends Parent<Y1, Y2> {}",
                "class GrandChild<Z1, Z2> extends Child<Z1, Z2> {}",
                "class A {}",
                "class B extends A {}",
                "class C extends A {}",
                "class D extends C {}",
                "class ChildBA extends Child<B, A> {}",
                "class ChildCA extends Child<C, A> {}",
                "class GrandChildDA extends GrandChild<D, D> {}");

        ResolvedType childBA = types.get(7);
        ResolvedType childCA = types.get(8);
        ResolvedType grandChildDD = types.get(9);

        // lcp(Child<B, A>, Child<C, A>, Child<D, D>) = Child<lcta(lcta(B, C), D), lcta(lcta(A, A), D)>
        ResolvedType lub = leastUpperBound(childBA, childCA, grandChildDD);
        assertEquals("Child<? extends A, ? extends A>", lub.describe());
    }

    @Test
    public void lub_of_generics_infinite_types() {
        List<ResolvedType> types = declaredTypes(
                "class Parent<X> {}",
                "class Child<Y> extends Parent<Y> {}",
                "class ChildInteger extends Child<Integer> {}",
                "class ChildString extends Child<String> {}");

        ResolvedType childInteger = types.get(2);
        ResolvedType childString = types.get(3);

        // lub(Integer, String) is an infinite type (Comparable<? extends lub(Integer, String)>), approximated by
        // the first minimal erased candidate
        ResolvedType lub = leastUpperBound(childInteger, childString);
        assertEquals("Child<? extends java.io.Serializable>", lub.describe());
    }

    private List<ResolvedType> types(String... types) {
        return Arrays.stream(types).map(type -> type(type)).collect(Collectors.toList());
    }

    private ResolvedType type(String type) {
        return new ReferenceTypeImpl(typeSolver.solveType(type));
    }

    private ResolvedType genericType(String type, String... parameterTypes) {
        return new ReferenceTypeImpl(typeSolver.solveType(type), types(parameterTypes));
    }

    private ResolvedType genericType(String type, ResolvedType... parameterTypes) {
        return new ReferenceTypeImpl(typeSolver.solveType(type), Arrays.asList(parameterTypes));
    }

    private ResolvedType extendsBound(String type) {
        return ResolvedWildcard.extendsBound(type(type));
    }

    private ResolvedType superBound(String type) {
        return ResolvedWildcard.superBound(type(type));
    }

    private ResolvedType unbound() {
        return ResolvedWildcard.UNBOUNDED;
    }

    private Set<ResolvedType> toSet(ResolvedType... resolvedTypes) {
        return new HashSet<>(Arrays.asList(resolvedTypes));
    }

    private ResolvedType leastUpperBound(ResolvedType... types) {
        return TypeHelper.leastUpperBound(toSet(types), typeSolver);
    }

    private List<ResolvedType> declaredTypes(String... lines) {
        CompilationUnit tree = treeOf(lines);
        List<ResolvedType> results = Lists.newLinkedList();
        for (ClassOrInterfaceDeclaration classTree : tree.findAll(ClassOrInterfaceDeclaration.class)) {
            results.add(new ReferenceTypeImpl(classTree.resolve()));
        }
        return results;
    }

    private ResolvedType declaredFieldType(String... lines) {
        return treeOf(lines).findFirst(FieldDeclaration.class).get().resolve().getType();
    }

    private ResolvedType declaredMethodReturnType(String... lines) {
        return treeOf(lines).findFirst(MethodDeclaration.class).get().resolve().getReturnType();
    }

    private List<ResolvedType> declaredMethodParameterTypes(String... lines) {
        return treeOf(lines).findFirst(MethodDeclaration.class).get().getParameters().stream()
                .map(parameter -> parameter.resolve().getType())
                .collect(Collectors.toList());
    }

    private List<ResolvedType> declaredEnumTypes(String... lines) {
        CompilationUnit tree = treeOf(lines);
        List<ResolvedType> results = Lists.newLinkedList();
        for (EnumDeclaration classTree : tree.findAll(EnumDeclaration.class)) {
            results.add(new ReferenceTypeImpl(classTree.resolve()));
        }
        return results;
    }

    private CompilationUnit treeOf(String... lines) {
        StringBuilder builder = new StringBuilder();
        for (String line : lines) {
            builder.append(line).append(System.lineSeparator());
        }
        return parser.parse(builder.toString());
    }
}
