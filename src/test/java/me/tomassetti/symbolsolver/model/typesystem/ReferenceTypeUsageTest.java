package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ReferenceTypeUsageTest {

    private ArrayTypeUsage arrayOfBooleans;
    private ArrayTypeUsage arrayOfStrings;
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
        arrayOfBooleans = new ArrayTypeUsage(PrimitiveTypeUsage.BOOLEAN);
        arrayOfStrings = new ArrayTypeUsage(string);
        listOfA = new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeParameterUsage(TypeParameter.onClass("A", "foo.Bar", Collections.emptyList()))), typeSolver);
        listOfStrings = new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);
        /*listOfWildcardExtendingString = new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new WildcardUsage()new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver);*/
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
    public void testIsAssignableBy() {
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

        assertEquals(false, listOfStrings.isAssignableBy(listOfWildcardExtendsString));
        assertEquals(false, listOfStrings.isAssignableBy(listOfWildcardExtendsString));
        assertEquals(true,  listOfWildcardExtendsString.isAssignableBy(listOfStrings));
        assertEquals(false, listOfWildcardExtendsString.isAssignableBy(listOfWildcardSuperString));
        assertEquals(true,  listOfWildcardSuperString.isAssignableBy(listOfStrings));
        assertEquals(false, listOfWildcardSuperString.isAssignableBy(listOfWildcardExtendsString));

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

}
