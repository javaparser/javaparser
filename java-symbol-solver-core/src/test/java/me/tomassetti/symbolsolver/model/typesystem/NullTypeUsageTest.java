package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.model.resolution.TypeParameter;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class NullTypeUsageTest {

    private ArrayTypeUsage arrayOfBooleans;
    private ArrayTypeUsage arrayOfListOfA;
    private ReferenceTypeUsageImpl OBJECT;
    private ReferenceTypeUsageImpl STRING;
    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
        OBJECT = new ReferenceTypeUsageImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeUsageImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ArrayTypeUsage(PrimitiveTypeUsage.BOOLEAN);
        arrayOfListOfA = new ArrayTypeUsage(new ReferenceTypeUsageImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeParameterUsage(TypeParameter.onClass("A", "foo.Bar", Collections.emptyList()))), typeSolver));
    }

    @Test
    public void testIsArray() {
        assertEquals(false, NullTypeUsage.INSTANCE.isArray());
    }

    @Test
    public void testIsPrimitive() {
        assertEquals(false, NullTypeUsage.INSTANCE.isPrimitive());
    }

    @Test
    public void testIsNull() {
        assertEquals(true, NullTypeUsage.INSTANCE.isNull());
    }

    @Test
    public void testIsReference() {
        assertEquals(true, NullTypeUsage.INSTANCE.isReference());
    }

    @Test
    public void testIsReferenceType() {
        assertEquals(false, NullTypeUsage.INSTANCE.isReferenceType());
    }

    @Test
    public void testIsVoid() {
        assertEquals(false, NullTypeUsage.INSTANCE.isVoid());
    }

    @Test
    public void testIsTypeVariable() {
        assertEquals(false, NullTypeUsage.INSTANCE.isTypeVariable());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsReferenceTypeUsage() {
        NullTypeUsage.INSTANCE.asReferenceTypeUsage();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsTypeParameter() {
        NullTypeUsage.INSTANCE.asTypeParameter();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsArrayTypeUsage() {
        NullTypeUsage.INSTANCE.asArrayTypeUsage();
    }

    @Test
    public void testAsDescribe() {
        assertEquals("null", NullTypeUsage.INSTANCE.describe());
    }

    @Test
    public void testReplaceParam() {
        assertTrue(NullTypeUsage.INSTANCE == NullTypeUsage.INSTANCE.replaceParam("A", OBJECT));
    }

    @Test
    public void testIsAssignableBy() {
        try {
            assertEquals(false, NullTypeUsage.INSTANCE.isAssignableBy(NullTypeUsage.INSTANCE));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, NullTypeUsage.INSTANCE.isAssignableBy(OBJECT));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, NullTypeUsage.INSTANCE.isAssignableBy(STRING));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, NullTypeUsage.INSTANCE.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, NullTypeUsage.INSTANCE.isAssignableBy(VoidTypeUsage.INSTANCE));
            fail();
        } catch (UnsupportedOperationException e) {

        }
    }

}
