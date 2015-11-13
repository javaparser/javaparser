package me.tomassetti.symbolsolver.model.typesystem;

import com.google.common.collect.ImmutableList;
import me.tomassetti.symbolsolver.resolution.TypeParameter;
import me.tomassetti.symbolsolver.resolution.TypeSolver;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import me.tomassetti.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.typesolvers.JreTypeSolver;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class PrimitiveTypeUsageTest {

    private ArrayTypeUsage arrayOfBooleans;
    private ArrayTypeUsage arrayOfListOfA;
    private ReferenceTypeUsage OBJECT;
    private ReferenceTypeUsage STRING;
    private TypeSolver typeSolver;
    
    private ReferenceTypeUsage booleanBox;
    private ReferenceTypeUsage characterBox;
    private ReferenceTypeUsage byteBox;
    private ReferenceTypeUsage shortBox;
    private ReferenceTypeUsage integerBox;
    private ReferenceTypeUsage longBox;
    private ReferenceTypeUsage floatBox;
    private ReferenceTypeUsage doubleBox;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
        OBJECT = new ReferenceTypeUsage(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeUsage(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ArrayTypeUsage(PrimitiveTypeUsage.BOOLEAN);
        arrayOfListOfA = new ArrayTypeUsage(new ReferenceTypeUsage(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeParameterUsage(TypeParameter.onClass("A", "foo.Bar", Collections.emptyList()))), typeSolver));
        
        booleanBox = new ReferenceTypeUsage(new ReflectionClassDeclaration(Boolean.class, typeSolver), typeSolver);
        characterBox = new ReferenceTypeUsage(new ReflectionClassDeclaration(Character.class, typeSolver), typeSolver);
        byteBox = new ReferenceTypeUsage(new ReflectionClassDeclaration(Byte.class, typeSolver), typeSolver);
        shortBox = new ReferenceTypeUsage(new ReflectionClassDeclaration(Short.class, typeSolver), typeSolver);
        integerBox = new ReferenceTypeUsage(new ReflectionClassDeclaration(Integer.class, typeSolver), typeSolver);
        longBox = new ReferenceTypeUsage(new ReflectionClassDeclaration(Long.class, typeSolver), typeSolver);
        floatBox = new ReferenceTypeUsage(new ReflectionClassDeclaration(Float.class, typeSolver), typeSolver);
        doubleBox = new ReferenceTypeUsage(new ReflectionClassDeclaration(Double.class, typeSolver), typeSolver);
        
    }

    @Test
    public void testIsArray() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertEquals(false, ptu.isArray());
        }
    }

    @Test
    public void testIsPrimitive() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertEquals(true, ptu.isPrimitive());
        }
    }

    @Test
    public void testIsNull() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertEquals(false, ptu.isNull());
        }
    }

    @Test
    public void testIsReference() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertEquals(false, ptu.isReference());
        }
    }

    @Test
    public void testIsReferenceType() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertEquals(false, ptu.isReferenceType());
        }
    }

    @Test
    public void testIsVoid() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertEquals(false, ptu.isVoid());
        }
    }

    @Test
    public void testIsTypeVariable() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertEquals(false, ptu.isTypeVariable());
        }
    }

    @Test
    public void testAsReferenceTypeUsage() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            try {
                ptu.asReferenceTypeUsage();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    public void testAsTypeParameter() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            try {
                ptu.asTypeParameter();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    public void testAsArrayTypeUsage() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            try {
                ptu.asArrayTypeUsage();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    public void testAsDescribe() {
        assertEquals("boolean", PrimitiveTypeUsage.BOOLEAN.describe());
        assertEquals("char", PrimitiveTypeUsage.CHAR.describe());
        assertEquals("byte", PrimitiveTypeUsage.BYTE.describe());
        assertEquals("short", PrimitiveTypeUsage.SHORT.describe());
        assertEquals("int", PrimitiveTypeUsage.INT.describe());
        assertEquals("long", PrimitiveTypeUsage.LONG.describe());
        assertEquals("float", PrimitiveTypeUsage.FLOAT.describe());
        assertEquals("double", PrimitiveTypeUsage.DOUBLE.describe());
    }

    @Test
    public void testReplaceParam() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertTrue(ptu == ptu.replaceParam("A", OBJECT));
        }
    }

    @Test
    public void testIsAssignableByOtherPrimitiveTypes() {
        assertEquals(true, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(PrimitiveTypeUsage.CHAR));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(PrimitiveTypeUsage.BYTE));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(PrimitiveTypeUsage.SHORT));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(PrimitiveTypeUsage.INT));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(PrimitiveTypeUsage.LONG));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(PrimitiveTypeUsage.FLOAT));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(PrimitiveTypeUsage.DOUBLE));

        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
        assertEquals(true, PrimitiveTypeUsage.CHAR.isAssignableBy(PrimitiveTypeUsage.CHAR));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(PrimitiveTypeUsage.BYTE));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(PrimitiveTypeUsage.SHORT));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(PrimitiveTypeUsage.INT));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(PrimitiveTypeUsage.LONG));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(PrimitiveTypeUsage.FLOAT));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(PrimitiveTypeUsage.DOUBLE));

        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(PrimitiveTypeUsage.CHAR));
        assertEquals(true, PrimitiveTypeUsage.BYTE.isAssignableBy(PrimitiveTypeUsage.BYTE));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(PrimitiveTypeUsage.SHORT));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(PrimitiveTypeUsage.INT));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(PrimitiveTypeUsage.LONG));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(PrimitiveTypeUsage.FLOAT));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(PrimitiveTypeUsage.DOUBLE));

        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(PrimitiveTypeUsage.CHAR));
        assertEquals(true, PrimitiveTypeUsage.SHORT.isAssignableBy(PrimitiveTypeUsage.BYTE));
        assertEquals(true, PrimitiveTypeUsage.SHORT.isAssignableBy(PrimitiveTypeUsage.SHORT));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(PrimitiveTypeUsage.INT));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(PrimitiveTypeUsage.LONG));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(PrimitiveTypeUsage.FLOAT));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(PrimitiveTypeUsage.DOUBLE));

        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(PrimitiveTypeUsage.CHAR));
        assertEquals(true, PrimitiveTypeUsage.INT.isAssignableBy(PrimitiveTypeUsage.BYTE));
        assertEquals(true, PrimitiveTypeUsage.INT.isAssignableBy(PrimitiveTypeUsage.SHORT));
        assertEquals(true, PrimitiveTypeUsage.INT.isAssignableBy(PrimitiveTypeUsage.INT));
        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(PrimitiveTypeUsage.LONG));
        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(PrimitiveTypeUsage.FLOAT));
        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(PrimitiveTypeUsage.DOUBLE));

        assertEquals(false, PrimitiveTypeUsage.LONG.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
        assertEquals(false, PrimitiveTypeUsage.LONG.isAssignableBy(PrimitiveTypeUsage.CHAR));
        assertEquals(true, PrimitiveTypeUsage.LONG.isAssignableBy(PrimitiveTypeUsage.BYTE));
        assertEquals(true, PrimitiveTypeUsage.LONG.isAssignableBy(PrimitiveTypeUsage.SHORT));
        assertEquals(true, PrimitiveTypeUsage.LONG.isAssignableBy(PrimitiveTypeUsage.INT));
        assertEquals(true, PrimitiveTypeUsage.LONG.isAssignableBy(PrimitiveTypeUsage.LONG));
        assertEquals(false, PrimitiveTypeUsage.LONG.isAssignableBy(PrimitiveTypeUsage.FLOAT));
        assertEquals(false, PrimitiveTypeUsage.LONG.isAssignableBy(PrimitiveTypeUsage.DOUBLE));

        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(PrimitiveTypeUsage.CHAR));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(PrimitiveTypeUsage.BYTE));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(PrimitiveTypeUsage.SHORT));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(PrimitiveTypeUsage.INT));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(PrimitiveTypeUsage.LONG));
        assertEquals(true, PrimitiveTypeUsage.FLOAT.isAssignableBy(PrimitiveTypeUsage.FLOAT));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(PrimitiveTypeUsage.DOUBLE));

        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(PrimitiveTypeUsage.BOOLEAN));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(PrimitiveTypeUsage.CHAR));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(PrimitiveTypeUsage.BYTE));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(PrimitiveTypeUsage.SHORT));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(PrimitiveTypeUsage.INT));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(PrimitiveTypeUsage.LONG));
        assertEquals(true, PrimitiveTypeUsage.DOUBLE.isAssignableBy(PrimitiveTypeUsage.FLOAT));
        assertEquals(true, PrimitiveTypeUsage.DOUBLE.isAssignableBy(PrimitiveTypeUsage.DOUBLE));
    }

    @Test
    public void testIsAssignableByBoxedTypes() {
        assertEquals(true, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(characterBox));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(longBox));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveTypeUsage.BOOLEAN.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(booleanBox));
        assertEquals(true, PrimitiveTypeUsage.CHAR.isAssignableBy(characterBox));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(longBox));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveTypeUsage.CHAR.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(characterBox));
        assertEquals(true, PrimitiveTypeUsage.BYTE.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(longBox));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveTypeUsage.BYTE.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(characterBox));
        assertEquals(true, PrimitiveTypeUsage.SHORT.isAssignableBy(byteBox));
        assertEquals(true, PrimitiveTypeUsage.SHORT.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(longBox));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveTypeUsage.SHORT.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(characterBox));
        assertEquals(true, PrimitiveTypeUsage.INT.isAssignableBy(byteBox));
        assertEquals(true, PrimitiveTypeUsage.INT.isAssignableBy(shortBox));
        assertEquals(true, PrimitiveTypeUsage.INT.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(longBox));
        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveTypeUsage.INT.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveTypeUsage.LONG.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveTypeUsage.LONG.isAssignableBy(characterBox));
        assertEquals(true, PrimitiveTypeUsage.LONG.isAssignableBy(byteBox));
        assertEquals(true, PrimitiveTypeUsage.LONG.isAssignableBy(shortBox));
        assertEquals(true, PrimitiveTypeUsage.LONG.isAssignableBy(integerBox));
        assertEquals(true, PrimitiveTypeUsage.LONG.isAssignableBy(longBox));
        assertEquals(false, PrimitiveTypeUsage.LONG.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveTypeUsage.LONG.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(characterBox));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(longBox));
        assertEquals(true, PrimitiveTypeUsage.FLOAT.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveTypeUsage.FLOAT.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(characterBox));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveTypeUsage.DOUBLE.isAssignableBy(longBox));
        assertEquals(true, PrimitiveTypeUsage.DOUBLE.isAssignableBy(floatBox));
        assertEquals(true, PrimitiveTypeUsage.DOUBLE.isAssignableBy(doubleBox));        
    }

    @Test
    public void testIsAssignableByAnythingElse() {
        for (PrimitiveTypeUsage ptu : PrimitiveTypeUsage.ALL) {
            assertEquals(false, ptu.isAssignableBy(OBJECT));
            assertEquals(false, ptu.isAssignableBy(STRING));
            assertEquals(false, ptu.isAssignableBy(NullTypeUsage.INSTANCE));
            assertEquals(false, ptu.isAssignableBy(VoidTypeUsage.INSTANCE));
            assertEquals(false, ptu.isAssignableBy(arrayOfBooleans));
            assertEquals(false, ptu.isAssignableBy(arrayOfListOfA));
        }
    }

}
