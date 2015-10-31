package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class VoidTypeUsageTest {

    private ArrayTypeUsage arrayOfBooleans;
    private ArrayTypeUsage arrayOfListOfA;
    private ReferenceTypeUsage OBJECT;
    private ReferenceTypeUsage STRING;
    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
        OBJECT = new ReferenceTypeUsage(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ArrayTypeUsage(PrimitiveTypeUsage.BOOLEAN);
        arrayOfListOfA = new ArrayTypeUsage(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeParameterUsage(TypeParameter.onClass("A", "foo.Bar", Collections.emptyList()))), typeSolver));
    }

    @Test
    public void testIsArray() {
        assertEquals(false, VoidTypeUsage.INSTANCE.isArray());
    }

    @Test
    public void testIsPrimitive() {
        assertEquals(false, VoidTypeUsage.INSTANCE.isPrimitive());
    }

    @Test
    public void testIsNull() {
        assertEquals(false, VoidTypeUsage.INSTANCE.isNull());
    }

    @Test
    public void testIsReference() {
        assertEquals(false, VoidTypeUsage.INSTANCE.isReference());
    }

    @Test
    public void testIsReferenceType() {
        assertEquals(false, VoidTypeUsage.INSTANCE.isReferenceType());
    }

    @Test
    public void testIsVoid() {
        assertEquals(true, VoidTypeUsage.INSTANCE.isVoid());
    }

    @Test
    public void testIsTypeVariable() {
        assertEquals(false, VoidTypeUsage.INSTANCE.isTypeVariable());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsReferenceTypeUsage() {
        VoidTypeUsage.INSTANCE.asReferenceTypeUsage();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsTypeParameter() {
        VoidTypeUsage.INSTANCE.asTypeParameter();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsArrayTypeUsage() {
        VoidTypeUsage.INSTANCE.asArrayTypeUsage();
    }

    @Test
    public void testAsDescribe() {
        assertEquals("void", VoidTypeUsage.INSTANCE.describe());
    }

    @Test
    public void testReplaceParam() {
        assertTrue(VoidTypeUsage.INSTANCE == VoidTypeUsage.INSTANCE.replaceParam("A", OBJECT));
    }

    @Test
    public void testIsAssignableBy() {
        try {
            assertEquals(false, VoidTypeUsage.INSTANCE.isAssignableBy(NullTypeUsage.INSTANCE));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, VoidTypeUsage.INSTANCE.isAssignableBy(OBJECT));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, VoidTypeUsage.INSTANCE.isAssignableBy(STRING));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, VoidTypeUsage.INSTANCE.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, VoidTypeUsage.INSTANCE.isAssignableBy(VoidTypeUsage.INSTANCE));
            fail();
        } catch (UnsupportedOperationException e) {

        }
    }

}
