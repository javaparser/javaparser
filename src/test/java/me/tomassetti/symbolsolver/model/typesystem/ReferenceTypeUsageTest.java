package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.util.*;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.*;

public class ReferenceTypeUsageTest {

    private ReferenceTypeUsage listOfA;
    private ReferenceTypeUsage listOfStrings;
    private ReferenceTypeUsage linkedListOfString;
    private ReferenceTypeUsage collectionOfString;
    private ReferenceTypeUsage listOfWildcardExtendsString;
    private ReferenceTypeUsage listOfWildcardSuperString;
    private ReferenceTypeUsage object;
    private ReferenceTypeUsage string;
    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
        object = new ReferenceTypeUsage(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        string = new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        listOfA = new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeParameterUsage(TypeParameter.onClass("A", "foo.Bar", Collections.emptyList()))), typeSolver);
        listOfStrings = new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);
        linkedListOfString = new ReferenceTypeUsage(
                new ReflectionClassDeclaration(LinkedList.class, typeSolver),
                ImmutableList.of(new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);
        collectionOfString = new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(Collection.class, typeSolver),
                ImmutableList.of(new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);
        listOfWildcardExtendsString = new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(WildcardUsage.extendsBound(string)), typeSolver);
        listOfWildcardSuperString = new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(WildcardUsage.superBound(string)), typeSolver);
    }

    @Test
    public void testIsArray() {
        assertEquals(false, object.isArray());
        assertEquals(false, string.isArray());
        assertEquals(false, listOfA.isArray());
        assertEquals(false, listOfStrings.isArray());
    }

    @Test
    public void testIsPrimitive() {
        assertEquals(false, object.isPrimitive());
        assertEquals(false, string.isPrimitive());
        assertEquals(false, listOfA.isPrimitive());
        assertEquals(false, listOfStrings.isPrimitive());
    }

    @Test
    public void testIsNull() {
        assertEquals(false, object.isNull());
        assertEquals(false, string.isNull());
        assertEquals(false, listOfA.isNull());
        assertEquals(false, listOfStrings.isNull());
    }

    @Test
    public void testIsReference() {
        assertEquals(true, object.isReference());
        assertEquals(true, string.isReference());
        assertEquals(true, listOfA.isReference());
        assertEquals(true, listOfStrings.isReference());
    }

    @Test
    public void testIsReferenceType() {
        assertEquals(true, object.isReferenceType());
        assertEquals(true, string.isReferenceType());
        assertEquals(true, listOfA.isReferenceType());
        assertEquals(true, listOfStrings.isReferenceType());
    }

    @Test
    public void testIsVoid() {
        assertEquals(false, object.isVoid());
        assertEquals(false, string.isVoid());
        assertEquals(false, listOfA.isVoid());
        assertEquals(false, listOfStrings.isVoid());
    }

    @Test
    public void testIsTypeVariable() {
        assertEquals(false, object.isTypeVariable());
        assertEquals(false, string.isTypeVariable());
        assertEquals(false, listOfA.isTypeVariable());
        assertEquals(false, listOfStrings.isTypeVariable());
    }

    @Test
    public void testAsReferenceTypeUsage() {
        assertTrue(object == object.asReferenceTypeUsage());
        assertTrue(string == string.asReferenceTypeUsage());
        assertTrue(listOfA == listOfA.asReferenceTypeUsage());
        assertTrue(listOfStrings == listOfStrings.asReferenceTypeUsage());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsTypeParameter() {
        object.asTypeParameter();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsArrayTypeUsage() {
        object.asArrayTypeUsage();
    }

    @Test
    public void testAsDescribe() {
        assertEquals("java.lang.Object", object.describe());
        assertEquals("java.lang.String", string.describe());
        assertEquals("java.util.List<A>", listOfA.describe());
        assertEquals("java.util.List<java.lang.String>", listOfStrings.describe());
    }

    @Test
    public void testReplaceParam() {
        assertTrue(object == object.replaceParam("A", object));
        assertTrue(string == string.replaceParam("A", object));
        assertTrue(listOfStrings == listOfStrings.replaceParam("A", object));
        assertEquals(listOfStrings, listOfA.replaceParam("A", string));
    }

    @Test
    public void testIsAssignableBySimple() {
        assertEquals(true, object.isAssignableBy(string));
        assertEquals(false, string.isAssignableBy(object));
        assertEquals(false, listOfStrings.isAssignableBy(listOfA));
        assertEquals(false, listOfA.isAssignableBy(listOfStrings));

        assertEquals(false, object.isAssignableBy(VoidTypeUsage.INSTANCE));
        assertEquals(false, string.isAssignableBy(VoidTypeUsage.INSTANCE));
        assertEquals(false, listOfStrings.isAssignableBy(VoidTypeUsage.INSTANCE));
        assertEquals(false, listOfA.isAssignableBy(VoidTypeUsage.INSTANCE));

        assertEquals(true, object.isAssignableBy(NullTypeUsage.INSTANCE));
        assertEquals(true, string.isAssignableBy(NullTypeUsage.INSTANCE));
        assertEquals(true, listOfStrings.isAssignableBy(NullTypeUsage.INSTANCE));
        assertEquals(true, listOfA.isAssignableBy(NullTypeUsage.INSTANCE));
    }

    @Test
    public void testIsAssignableByGenerics() {
        assertEquals(false, listOfStrings.isAssignableBy(listOfWildcardExtendsString));
        assertEquals(false, listOfStrings.isAssignableBy(listOfWildcardExtendsString));
        assertEquals(true,  listOfWildcardExtendsString.isAssignableBy(listOfStrings));
        assertEquals(false, listOfWildcardExtendsString.isAssignableBy(listOfWildcardSuperString));
        assertEquals(true,  listOfWildcardSuperString.isAssignableBy(listOfStrings));
        assertEquals(false, listOfWildcardSuperString.isAssignableBy(listOfWildcardExtendsString));
    }

    @Test
    public void testIsAssignableByGenericsInheritance() {
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
    public void testGetAllAncestorsConsideringTypeParameters() {
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
    public void testGetAllAncestorsConsideringGenericsCases() {
        ReferenceTypeUsage foo = new ReferenceTypeUsage(new ReflectionClassDeclaration(Foo.class, typeSolver), typeSolver);
        ReferenceTypeUsage bar = new ReferenceTypeUsage(new ReflectionClassDeclaration(Bar.class, typeSolver), typeSolver);
        ReferenceTypeUsage left, right;

        //YES MoreBazzing<Foo, Bar> e1 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeUsage(
                    new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                    ImmutableList.of(foo, bar), typeSolver)
                .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES MoreBazzing<? extends Foo, Bar> e2 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(WildcardUsage.extendsBound(foo), bar), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES MoreBazzing<Foo, ? extends Bar> e3 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(foo, WildcardUsage.extendsBound(bar)), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES MoreBazzing<? extends Foo, ? extends Foo> e4 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                        ImmutableList.of(WildcardUsage.extendsBound(foo), WildcardUsage.extendsBound(foo)), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES MoreBazzing<? extends Foo, ? extends Foo> e5 = new MoreBazzing<Bar, Bar>();
        left = new ReferenceTypeUsage(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(WildcardUsage.extendsBound(foo), WildcardUsage.extendsBound(foo)), typeSolver);
        right = new ReferenceTypeUsage(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(bar, bar), typeSolver);
        assertEquals(true, left.isAssignableBy(right));

        //YES Bazzer<Object, String, String> e6 = new MoreBazzing<String, Object>();
        left = new ReferenceTypeUsage(
                new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                ImmutableList.of(object, string, string), typeSolver);
        right = new ReferenceTypeUsage(
                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                ImmutableList.of(string, object), typeSolver);
        assertEquals(true, left.isAssignableBy(right));

        //YES Bazzer<String,String,String> e7 = new MoreBazzing<String, String>();
        assertEquals(true,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(string, string, string), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(string, string), typeSolver))
        );

        //YES Bazzer<Bar,String,Foo> e8 = new MoreBazzing<Foo, Bar>();
        assertEquals(true,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar, string, foo), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(foo, bar), typeSolver))
        );

        //YES Bazzer<Foo,String,Bar> e9 = new MoreBazzing<Bar, Foo>();
        assertEquals(true,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(foo, string, bar), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo), typeSolver))
        );

        //NO Bazzer<Bar,String,Foo> n1 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar,string,foo), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo), typeSolver))
        );

        //NO Bazzer<Bar,String,Bar> n2 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(bar, string, foo), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo), typeSolver))
        );

        //NO Bazzer<Foo,Object,Bar> n3 = new MoreBazzing<Bar, Foo>();
        assertEquals(false,
                new ReferenceTypeUsage(
                        new ReflectionClassDeclaration(Bazzer.class, typeSolver),
                        ImmutableList.of(foo, object, bar), typeSolver)
                        .isAssignableBy(new ReferenceTypeUsage(
                                new ReflectionClassDeclaration(MoreBazzing.class, typeSolver),
                                ImmutableList.of(bar, foo), typeSolver))
        );
    }

}
