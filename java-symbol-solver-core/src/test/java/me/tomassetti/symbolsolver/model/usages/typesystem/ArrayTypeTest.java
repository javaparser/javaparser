package me.tomassetti.symbolsolver.model.usages.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.model.declarations.TypeParameterDeclaration;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.lang.Object;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class ArrayTypeTest {

    private ArrayType arrayOfBooleans;
    private ArrayType arrayOfStrings;
    private ArrayType arrayOfListOfA;
    private ArrayType arrayOfListOfStrings;
    private ReferenceTypeImpl OBJECT;
    private ReferenceTypeImpl STRING;
    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
        OBJECT = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ArrayType(PrimitiveType.BOOLEAN);
        arrayOfStrings = new ArrayType(STRING);
        arrayOfListOfA = new ArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeParameter(TypeParameterDeclaration.onClass("A", "foo.Bar", Collections.emptyList()))), typeSolver));
        arrayOfListOfStrings = new ArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver));
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
        arrayOfBooleans.asReferenceType();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsTypeParameter() {
        arrayOfBooleans.asTypeParameter();
    }

    @Test(expected = UnsupportedOperationException.class)
    public void testAsPrimitive() {
        arrayOfBooleans.asPrimitive();
    }

    @Test
    public void testAsArrayTypeUsage() {
        assertTrue(arrayOfBooleans == arrayOfBooleans.asArrayType());
        assertTrue(arrayOfStrings == arrayOfStrings.asArrayType());
        assertTrue(arrayOfListOfA == arrayOfListOfA.asArrayType());
    }

    @Test
    public void testAsDescribe() {
        assertEquals("boolean[]", arrayOfBooleans.describe());
        assertEquals("java.lang.String[]", arrayOfStrings.describe());
    }

    @Test
    public void testReplaceParam() {
        assertTrue(arrayOfBooleans == arrayOfBooleans.replaceParam("A", OBJECT));
        assertTrue(arrayOfStrings == arrayOfStrings.replaceParam("A", OBJECT));
        assertTrue(arrayOfListOfStrings == arrayOfListOfStrings.replaceParam("A", OBJECT));
        ArrayType arrayOfListOfObjects = new ArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(OBJECT), typeSolver));
        assertEquals(true, arrayOfListOfA.replaceParam("A", OBJECT).isArray());
        assertEquals(ImmutableList.of(OBJECT),
                arrayOfListOfA.replaceParam("A", OBJECT).asArrayType().getComponentType()
                        .asReferenceType().typeParametersValues());
        assertEquals(new ReflectionInterfaceDeclaration(List.class, typeSolver),
                arrayOfListOfA.replaceParam("A", OBJECT).asArrayType().getComponentType()
                        .asReferenceType().getTypeDeclaration());
        assertEquals(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(OBJECT), typeSolver),
                arrayOfListOfA.replaceParam("A", OBJECT).asArrayType().getComponentType());
        assertEquals(arrayOfListOfObjects, arrayOfListOfA.replaceParam("A", OBJECT));
        assertEquals(arrayOfListOfStrings, arrayOfListOfA.replaceParam("A", STRING));
        assertTrue(arrayOfListOfA == arrayOfListOfA.replaceParam("B", OBJECT));
    }

    @Test
    public void testIsAssignableBy() {
        assertEquals(false, arrayOfBooleans.isAssignableBy(OBJECT));
        assertEquals(false, arrayOfBooleans.isAssignableBy(STRING));
        assertEquals(false, arrayOfBooleans.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(false, arrayOfBooleans.isAssignableBy(VoidType.INSTANCE));

        assertEquals(true, arrayOfBooleans.isAssignableBy(arrayOfBooleans));
        assertEquals(false, arrayOfBooleans.isAssignableBy(arrayOfStrings));
        assertEquals(false, arrayOfBooleans.isAssignableBy(arrayOfListOfA));
        assertEquals(false, arrayOfBooleans.isAssignableBy(arrayOfListOfStrings));
        assertEquals(false, arrayOfStrings.isAssignableBy(arrayOfBooleans));
        assertEquals(true, arrayOfStrings.isAssignableBy(arrayOfStrings));
        assertEquals(false, arrayOfStrings.isAssignableBy(arrayOfListOfA));
        assertEquals(false, arrayOfStrings.isAssignableBy(arrayOfListOfStrings));
        assertEquals(false, arrayOfListOfA.isAssignableBy(arrayOfBooleans));
        assertEquals(false, arrayOfListOfA.isAssignableBy(arrayOfStrings));
        assertEquals(true, arrayOfListOfA.isAssignableBy(arrayOfListOfA));
        assertEquals(false, arrayOfListOfA.isAssignableBy(arrayOfListOfStrings));
        assertEquals(false, arrayOfListOfStrings.isAssignableBy(arrayOfBooleans));
        assertEquals(false, arrayOfListOfStrings.isAssignableBy(arrayOfStrings));
        assertEquals(false, arrayOfListOfStrings.isAssignableBy(arrayOfListOfA));
        assertEquals(true, arrayOfListOfStrings.isAssignableBy(arrayOfListOfStrings));
    }

}
