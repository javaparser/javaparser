package me.tomassetti.symbolsolver.model.typesystem;

import com.github.javaparser.ast.type.ReferenceType;
import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.resolution.reflection.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;
import org.omg.CORBA.*;

import java.lang.Object;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class ArrayTypeUsageTest {

    private ArrayTypeUsage arrayOfBooleans;
    private ArrayTypeUsage arrayOfStrings;
    private ArrayTypeUsage arrayOfListOfA;
    private ArrayTypeUsage arrayOfListOfStrings;
    private ReferenceTypeUsage OBJECT;
    private ReferenceTypeUsage STRING;
    private TypeSolver typeSolver;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
        OBJECT = new ReferenceTypeUsage(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ArrayTypeUsage(PrimitiveTypeUsage.BOOLEAN);
        arrayOfStrings = new ArrayTypeUsage(STRING);
        arrayOfListOfA = new ArrayTypeUsage(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeUsageOfTypeParameter(TypeParameter.onClass("A", "foo.Bar", Collections.emptyList()))), typeSolver));
        arrayOfListOfStrings = new ArrayTypeUsage(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver)), typeSolver));
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
        assertTrue(arrayOfBooleans == arrayOfBooleans.replaceParam("A", OBJECT));
        assertTrue(arrayOfStrings == arrayOfStrings.replaceParam("A", OBJECT));
        assertTrue(arrayOfListOfStrings == arrayOfListOfStrings.replaceParam("A", OBJECT));
        ArrayTypeUsage arrayOfListOfObjects = new ArrayTypeUsage(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(OBJECT), typeSolver));
        assertEquals(true, arrayOfListOfA.replaceParam("A", OBJECT).isArray());
        assertEquals(ImmutableList.of(OBJECT),
                arrayOfListOfA.replaceParam("A", OBJECT).asArrayTypeUsage().getComponentType()
                        .asReferenceTypeUsage().parameters());
        assertEquals(new ReflectionInterfaceDeclaration(List.class, typeSolver),
                arrayOfListOfA.replaceParam("A", OBJECT).asArrayTypeUsage().getComponentType()
                        .asReferenceTypeUsage().getTypeDeclaration());
        assertEquals(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(OBJECT), typeSolver),
                arrayOfListOfA.replaceParam("A", OBJECT).asArrayTypeUsage().getComponentType());
        assertEquals(arrayOfListOfObjects, arrayOfListOfA.replaceParam("A", OBJECT));
        assertEquals(arrayOfListOfStrings, arrayOfListOfA.replaceParam("A", STRING));
        assertTrue(arrayOfListOfA == arrayOfListOfA.replaceParam("B", OBJECT));
    }

    @Test
    public void testIsAssignableBy() {
        //assertEquals(true, arrayOfBooleans.isAssignableBy(arrayOfBooleans, ));
    }

}
