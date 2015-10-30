package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionInterfaceDeclaration;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class ArrayTypeUsageTest {

    private ArrayTypeUsage arrayOfBooleans;
    private ArrayTypeUsage arrayOfStrings;
    private ArrayTypeUsage arrayOfListOfA;
    private ArrayTypeUsage arrayOfListOfStrings;

    @Before
    public void setup() {
        arrayOfBooleans = new ArrayTypeUsage(PrimitiveTypeUsage.BOOLEAN);
        arrayOfStrings = new ArrayTypeUsage(new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class)));
        arrayOfListOfA = new ArrayTypeUsage(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class),
                ImmutableList.of(new TypeUsageOfTypeParameter(TypeParameter.onClass("A", "foo.Bar", Collections.emptyList())))));
        arrayOfListOfStrings = new ArrayTypeUsage(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class),
                ImmutableList.of(new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class)))));
    }

    @Test
    public void testIsArray() {
        assertEquals(true, arrayOfBooleans.isArray());
        assertEquals(true, arrayOfStrings.isArray());
    }

    @Test
    public void testIsPrimitive() {
        assertEquals(false, arrayOfBooleans.isPrimitive());
        assertEquals(false, arrayOfStrings.isPrimitive());
    }

    @Test
    public void testIsNull() {
        assertEquals(false, arrayOfBooleans.isNull());
        assertEquals(false, arrayOfStrings.isNull());
    }

    @Test
    public void testIsReference() {
        assertEquals(true, arrayOfBooleans.isReference());
        assertEquals(true, arrayOfStrings.isReference());
    }

    @Test
    public void testIsReferenceType() {
        assertEquals(false, arrayOfBooleans.isReferenceType());
        assertEquals(false, arrayOfStrings.isReferenceType());
    }

    @Test
    public void testIsVoid() {
        assertEquals(false, arrayOfBooleans.isVoid());
        assertEquals(false, arrayOfStrings.isVoid());
    }

    @Test
    public void testIsTypeVariable() {
        assertEquals(false, arrayOfBooleans.isTypeVariable());
        assertEquals(false, arrayOfStrings.isTypeVariable());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsReferenceTypeUsage() {
        arrayOfBooleans.asReferenceTypeUsage();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsTypeParameter() {
        arrayOfBooleans.asTypeParameter();
    }

    @Test
    public void testAsArrayTypeUsage() {
        assertTrue(arrayOfBooleans == arrayOfBooleans.asArrayTypeUsage());
        assertTrue(arrayOfStrings == arrayOfStrings.asArrayTypeUsage());
        assertTrue(arrayOfListOfA == arrayOfListOfA.asArrayTypeUsage());
    }

    @Test
    public void testAsDescribe() {
        assertEquals("boolean[]", arrayOfBooleans.describe());
        assertEquals("java.lang.String[]", arrayOfStrings.describe());
    }

    @Test
    public void testReplaceParam() {
        assertTrue(arrayOfBooleans == arrayOfBooleans.replaceParam("A", ReferenceTypeUsage.OBJECT));
        assertTrue(arrayOfStrings == arrayOfStrings.replaceParam("A", ReferenceTypeUsage.OBJECT));
        assertTrue(arrayOfListOfStrings == arrayOfListOfStrings.replaceParam("A", ReferenceTypeUsage.OBJECT));
        ArrayTypeUsage arrayOfListOfObjects = new ArrayTypeUsage(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class),
                ImmutableList.of(ReferenceTypeUsage.OBJECT)));
        assertEquals(true, arrayOfListOfA.replaceParam("A", ReferenceTypeUsage.OBJECT).isArray());
        assertEquals(ImmutableList.of(ReferenceTypeUsage.OBJECT),
                arrayOfListOfA.replaceParam("A", ReferenceTypeUsage.OBJECT).asArrayTypeUsage().getComponentType()
                        .asReferenceTypeUsage().parameters());
        assertEquals(new ReflectionInterfaceDeclaration(List.class),
                arrayOfListOfA.replaceParam("A", ReferenceTypeUsage.OBJECT).asArrayTypeUsage().getComponentType()
                        .asReferenceTypeUsage().getTypeDeclaration());
        assertEquals(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class),
                ImmutableList.of(ReferenceTypeUsage.OBJECT)),
                arrayOfListOfA.replaceParam("A", ReferenceTypeUsage.OBJECT).asArrayTypeUsage().getComponentType());
        assertEquals(arrayOfListOfObjects, arrayOfListOfA.replaceParam("A", ReferenceTypeUsage.OBJECT));
        assertEquals(arrayOfListOfStrings, arrayOfListOfA.replaceParam("A", ReferenceTypeUsage.STRING));
        assertTrue(arrayOfListOfA == arrayOfListOfA.replaceParam("B", ReferenceTypeUsage.OBJECT));
    }

}
