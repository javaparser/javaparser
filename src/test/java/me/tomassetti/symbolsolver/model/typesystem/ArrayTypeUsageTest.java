package me.tomassetti.symbolsolver.model.typesystem;

import me.tomassetti.symbolsolver.resolution.reflection.ReflectionClassDeclaration;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

public class ArrayTypeUsageTest {

    private ArrayTypeUsage arrayOfBooleans;
    private ArrayTypeUsage arrayOfStrings;

    @Before
    public void setup() {
        arrayOfBooleans = new ArrayTypeUsage(PrimitiveTypeUsage.BOOLEAN);
        arrayOfStrings = new ArrayTypeUsage(new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class)));
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
    public void testAsDescribe() {
        assertEquals("boolean[]", arrayOfBooleans.describe());
        assertEquals("java.lang.String[]", arrayOfStrings.describe());
    }

}
