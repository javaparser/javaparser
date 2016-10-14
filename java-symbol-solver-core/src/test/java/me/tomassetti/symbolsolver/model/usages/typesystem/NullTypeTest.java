package me.tomassetti.symbolsolver.model.usages.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class NullTypeTest {

    private ArrayType arrayOfBooleans;
    private ArrayType arrayOfListOfA;
    private ReferenceTypeImpl OBJECT;
    private ReferenceTypeImpl STRING;
    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
        OBJECT = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ArrayType(PrimitiveType.BOOLEAN);
        arrayOfListOfA = new ArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeParameter(TypeParameterDeclaration.onClass("A", "foo.Bar", Collections.emptyList()))), typeSolver));
    }

    @Test
    public void testIsArray() {
        assertEquals(false, NullType.INSTANCE.isArray());
    }

    @Test
    public void testIsPrimitive() {
        assertEquals(false, NullType.INSTANCE.isPrimitive());
    }

    @Test
    public void testIsNull() {
        assertEquals(true, NullType.INSTANCE.isNull());
    }

    @Test
    public void testIsReference() {
        assertEquals(true, NullType.INSTANCE.isReference());
    }

    @Test
    public void testIsReferenceType() {
        assertEquals(false, NullType.INSTANCE.isReferenceType());
    }

    @Test
    public void testIsVoid() {
        assertEquals(false, NullType.INSTANCE.isVoid());
    }

    @Test
    public void testIsTypeVariable() {
        assertEquals(false, NullType.INSTANCE.isTypeVariable());
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsReferenceTypeUsage() {
        NullType.INSTANCE.asReferenceType();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsTypeParameter() {
        NullType.INSTANCE.asTypeParameter();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsArrayTypeUsage() {
        NullType.INSTANCE.asArrayType();
    }

    @Test
    public void testAsDescribe() {
        assertEquals("null", NullType.INSTANCE.describe());
    }

    @Test
    public void testReplaceParam() {
        assertTrue(NullType.INSTANCE == NullType.INSTANCE.replaceParam("A", OBJECT));
    }

    @Test
    public void testIsAssignableBy() {
        try {
            assertEquals(false, NullType.INSTANCE.isAssignableBy(NullType.INSTANCE));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, NullType.INSTANCE.isAssignableBy(OBJECT));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, NullType.INSTANCE.isAssignableBy(STRING));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, NullType.INSTANCE.isAssignableBy(PrimitiveType.BOOLEAN));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, NullType.INSTANCE.isAssignableBy(VoidType.INSTANCE));
            fail();
        } catch (UnsupportedOperationException e) {

        }
    }

}
