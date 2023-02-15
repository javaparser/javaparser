package com.github.javaparser.symbolsolver.resolution.typeinference;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOError;
import java.io.IOException;
import java.io.Serializable;
import java.rmi.AlreadyBoundException;
import java.rmi.activation.UnknownGroupException;
import java.util.*;
import java.util.stream.Collectors;

import org.junit.jupiter.api.*;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedWildcard;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.Lists;

class LeastUpperBoundTest {

    private TypeSolver typeSolver;

    @BeforeAll
    static void setUpBeforeClass() throws Exception {
        ParserConfiguration configuration = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        // Setup parser
        StaticJavaParser.setConfiguration(configuration);
    }

    @AfterAll
    static void tearDownAfterClass() throws Exception {
    }

    @BeforeEach
    void setUp() throws Exception {
        typeSolver = new ReflectionTypeSolver();
    }

    @AfterEach
    void tearDown() throws Exception {
    }

    @Test
    public void lub_of_one_element_is_itself() {
        ResolvedType exception = type(Exception.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(exception);
        assertEquals(lub, exception);
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
        List<ResolvedType> types = declaredTypes(
                "class A extends Exception {}",
                "class B {}");
        ResolvedType a = types.get(0);
        ResolvedType b = types.get(1);
        ResolvedType lub = leastUpperBound(a, b);
        ResolvedType expected = type("java.lang.Object");
        assertEquals(expected, lub);
    }

    @Test
    public void lub_approximation_inheritance_and_multiple_bounds() {
        List<ResolvedType> types = declaredTypes(
                "class A implements I1, I2 {}",
                "class B implements I2, I1 {}",
                "interface I1 {}",
                "interface I2 {}");
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
        // java.lang.Object/java.lang.Throwable/java.lang.Exception/java.rmi.AlreadyBoundException
        ResolvedType alreadyBoundException = type(AlreadyBoundException.class.getCanonicalName());
        // java.lang.Object//java.lang.Throwable/java.lang.Exception/java.rmi.activation.ActivationException/java.rmi.activation.UnknownGroupException
        ResolvedType unknownGroupException = type(UnknownGroupException.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(alreadyBoundException, unknownGroupException);
        assertEquals(expected, lub);
    }

    @Test
    public void lub_with_unknown_inheritance() {
        List<ResolvedType> types = declaredTypes(
                "class A extends Exception {}",
                "class B extends UnknownException {}");
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
        List<ResolvedType> types = declaredTypes(
                "class A<T> extends java.util.List<T> {}",
                "class B extends A<String> {}");
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
        ResolvedType expected = genericType(List.class.getCanonicalName(), Object.class.getCanonicalName());
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
        ResolvedType list1 = genericType(List.class.getCanonicalName(), extendsBound(Exception.class.getCanonicalName()));
        ResolvedType list2 = genericType(List.class.getCanonicalName(), superBound(Exception.class.getCanonicalName()));
        ResolvedType expected = genericType(List.class.getCanonicalName(), Exception.class.getCanonicalName());
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected.describe(), lub.describe());

    }

    @Test
    void lub_of_generics_with_bounded_type_in_hierarchy() {
        ResolvedType list1 = genericType(List.class.getCanonicalName(), Number.class.getCanonicalName());
        ResolvedType list2 = genericType(List.class.getCanonicalName(), Integer.class.getCanonicalName());
        ResolvedType expected = genericType(List.class.getCanonicalName(), extendsBound(Number.class.getCanonicalName()));
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    @Disabled("Waiting for generic type inheritance")
    // we have to find the inheritance tree for List<? extends Integer> or List<? extends Number>
    void lub_of_generics_with_upper_bounded_type_in_hierarchy() {
        ResolvedType list1 = genericType(List.class.getCanonicalName(), extendsBound(Number.class.getCanonicalName()));
        ResolvedType list2 = genericType(List.class.getCanonicalName(), extendsBound(Integer.class.getCanonicalName()));
        ResolvedType expected = genericType(List.class.getCanonicalName(), extendsBound(Number.class.getCanonicalName()));
        ResolvedType lub = leastUpperBound(list1, list2);
        assertEquals(expected.describe(), lub.describe());
    }

    @Test
    @Disabled("Waiting for generic type resolution")
    public void lub_of_generics_with_raw_type() {
        List<ResolvedType> types = declaredTypes(
                "class Parent<X> {}",
                "class Child<Y> extends Parent<Y> {}",
                "class ChildString extends Child<String> {}",
                "class ChildRaw extends Child {}");
        ResolvedType ChildString = types.get(2);
        ResolvedType ChildRaw = types.get(3);

        ResolvedType lub = leastUpperBound(ChildString, ChildRaw);
        ResolvedType expected = types.get(1);
        assertEquals(expected, lub);
    }

    @Test
    @Disabled("Waiting for generic type resolution")
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

        ResolvedType lub = leastUpperBound(ChildP, childC);
        System.out.println(lub.describe());
        assertEquals("Parent<Other<? extends A>>", lub.describe());
    }

    @Test
    @Disabled("Waiting for generic type resolution")
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

        ResolvedType lub = leastUpperBound(childBA, childCA, grandChildDD);
        System.out.println(lub.describe());
    }


	@Test
	@Disabled("Waiting for generic type resolution")
	public void lub_of_generics_without_loop2() {
		List<ResolvedType> typesFromInput = declaredTypes(
				"class Parent<X> {}",
				"class Child<Y> extends Parent<Y> {}",
				"class Other<Z> {}",
				"class A {}",
				"class ChildP extends Parent<Other<? extends A>> {}",
				"class ChildC extends Child<Other<? extends A>> {}");

		ResolvedType ChildP = typesFromInput.get(4);
		ResolvedType childC = typesFromInput.get(5);

		ResolvedType lub = leastUpperBound(ChildP, childC);
		System.out.println(lub.describe());
    }

	@Test
	@Disabled("Waiting for generic type resolution")
	public void lub_of_generics_infinite_types() {
		List<ResolvedType> types = declaredTypes(
				"class Parent<X> {}",
				"class Child<Y> extends Parent<Y> {}",
				"class ChildInteger extends Child<Integer> {}",
				"class ChildString extends Child<String> {}");

		ResolvedType childInteger = types.get(2);
		ResolvedType childString = types.get(3);

		ResolvedType lub = leastUpperBound(childInteger, childString);
		System.out.println(lub.describe());
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
        return TypeHelper.leastUpperBound(toSet(types));
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
