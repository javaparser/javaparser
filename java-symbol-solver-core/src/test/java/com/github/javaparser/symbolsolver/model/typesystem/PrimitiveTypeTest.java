/*
 * Copyright 2016 Federico Tomassetti
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.github.javaparser.symbolsolver.model.typesystem;

import com.github.javaparser.symbolsolver.model.declarations.TypeParameterDeclaration;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JreTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

public class PrimitiveTypeTest {

    private ArrayType arrayOfBooleans;
    private ArrayType arrayOfListOfA;
    private ReferenceTypeImpl OBJECT;
    private ReferenceTypeImpl STRING;
    private TypeSolver typeSolver;

    private ReferenceTypeImpl booleanBox;
    private ReferenceTypeImpl characterBox;
    private ReferenceTypeImpl byteBox;
    private ReferenceTypeImpl shortBox;
    private ReferenceTypeImpl integerBox;
    private ReferenceTypeImpl longBox;
    private ReferenceTypeImpl floatBox;
    private ReferenceTypeImpl doubleBox;

    @Before
    public void setup() {
        typeSolver = new JreTypeSolver();
        OBJECT = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ArrayType(PrimitiveType.BOOLEAN);
        arrayOfListOfA = new ArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new TypeVariable(TypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList()))), typeSolver));

        booleanBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Boolean.class, typeSolver), typeSolver);
        characterBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Character.class, typeSolver), typeSolver);
        byteBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Byte.class, typeSolver), typeSolver);
        shortBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Short.class, typeSolver), typeSolver);
        integerBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Integer.class, typeSolver), typeSolver);
        longBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Long.class, typeSolver), typeSolver);
        floatBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Float.class, typeSolver), typeSolver);
        doubleBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Double.class, typeSolver), typeSolver);

    }

    @Test
    public void testIsArray() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            assertEquals(false, ptu.isArray());
        }
    }

    @Test
    public void testIsPrimitive() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            assertEquals(true, ptu.isPrimitive());
        }
    }

    @Test
    public void testIsNull() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            assertEquals(false, ptu.isNull());
        }
    }

    @Test
    public void testIsReference() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            assertEquals(false, ptu.isReference());
        }
    }

    @Test
    public void testIsReferenceType() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            assertEquals(false, ptu.isReferenceType());
        }
    }

    @Test
    public void testIsVoid() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            assertEquals(false, ptu.isVoid());
        }
    }

    @Test
    public void testIsTypeVariable() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            assertEquals(false, ptu.isTypeVariable());
        }
    }

    @Test
    public void testAsReferenceTypeUsage() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            try {
                ptu.asReferenceType();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    public void testAsTypeParameter() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            try {
                ptu.asTypeParameter();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    public void testAsArrayTypeUsage() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            try {
                ptu.asArrayType();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    public void testAsDescribe() {
        assertEquals("boolean", PrimitiveType.BOOLEAN.describe());
        assertEquals("char", PrimitiveType.CHAR.describe());
        assertEquals("byte", PrimitiveType.BYTE.describe());
        assertEquals("short", PrimitiveType.SHORT.describe());
        assertEquals("int", PrimitiveType.INT.describe());
        assertEquals("long", PrimitiveType.LONG.describe());
        assertEquals("float", PrimitiveType.FLOAT.describe());
        assertEquals("double", PrimitiveType.DOUBLE.describe());
    }

    @Test
    public void testIsAssignableByOtherPrimitiveTypes() {
        assertEquals(true, PrimitiveType.BOOLEAN.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(PrimitiveType.CHAR));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(PrimitiveType.BYTE));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(PrimitiveType.SHORT));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(PrimitiveType.INT));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(PrimitiveType.LONG));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(PrimitiveType.FLOAT));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(PrimitiveType.DOUBLE));

        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(true, PrimitiveType.CHAR.isAssignableBy(PrimitiveType.CHAR));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(PrimitiveType.BYTE));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(PrimitiveType.SHORT));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(PrimitiveType.INT));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(PrimitiveType.LONG));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(PrimitiveType.FLOAT));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(PrimitiveType.DOUBLE));

        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(PrimitiveType.CHAR));
        assertEquals(true, PrimitiveType.BYTE.isAssignableBy(PrimitiveType.BYTE));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(PrimitiveType.SHORT));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(PrimitiveType.INT));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(PrimitiveType.LONG));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(PrimitiveType.FLOAT));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(PrimitiveType.DOUBLE));

        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(PrimitiveType.CHAR));
        assertEquals(true, PrimitiveType.SHORT.isAssignableBy(PrimitiveType.BYTE));
        assertEquals(true, PrimitiveType.SHORT.isAssignableBy(PrimitiveType.SHORT));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(PrimitiveType.INT));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(PrimitiveType.LONG));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(PrimitiveType.FLOAT));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(PrimitiveType.DOUBLE));

        assertEquals(false, PrimitiveType.INT.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(false, PrimitiveType.INT.isAssignableBy(PrimitiveType.CHAR));
        assertEquals(true, PrimitiveType.INT.isAssignableBy(PrimitiveType.BYTE));
        assertEquals(true, PrimitiveType.INT.isAssignableBy(PrimitiveType.SHORT));
        assertEquals(true, PrimitiveType.INT.isAssignableBy(PrimitiveType.INT));
        assertEquals(false, PrimitiveType.INT.isAssignableBy(PrimitiveType.LONG));
        assertEquals(false, PrimitiveType.INT.isAssignableBy(PrimitiveType.FLOAT));
        assertEquals(false, PrimitiveType.INT.isAssignableBy(PrimitiveType.DOUBLE));

        assertEquals(false, PrimitiveType.LONG.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(false, PrimitiveType.LONG.isAssignableBy(PrimitiveType.CHAR));
        assertEquals(true, PrimitiveType.LONG.isAssignableBy(PrimitiveType.BYTE));
        assertEquals(true, PrimitiveType.LONG.isAssignableBy(PrimitiveType.SHORT));
        assertEquals(true, PrimitiveType.LONG.isAssignableBy(PrimitiveType.INT));
        assertEquals(true, PrimitiveType.LONG.isAssignableBy(PrimitiveType.LONG));
        assertEquals(false, PrimitiveType.LONG.isAssignableBy(PrimitiveType.FLOAT));
        assertEquals(false, PrimitiveType.LONG.isAssignableBy(PrimitiveType.DOUBLE));

        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(PrimitiveType.CHAR));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(PrimitiveType.BYTE));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(PrimitiveType.SHORT));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(PrimitiveType.INT));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(PrimitiveType.LONG));
        assertEquals(true, PrimitiveType.FLOAT.isAssignableBy(PrimitiveType.FLOAT));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(PrimitiveType.DOUBLE));

        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(PrimitiveType.BOOLEAN));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(PrimitiveType.CHAR));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(PrimitiveType.BYTE));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(PrimitiveType.SHORT));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(PrimitiveType.INT));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(PrimitiveType.LONG));
        assertEquals(true, PrimitiveType.DOUBLE.isAssignableBy(PrimitiveType.FLOAT));
        assertEquals(true, PrimitiveType.DOUBLE.isAssignableBy(PrimitiveType.DOUBLE));
    }

    @Test
    public void testIsAssignableByBoxedTypes() {
        assertEquals(true, PrimitiveType.BOOLEAN.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(characterBox));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(longBox));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveType.BOOLEAN.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(booleanBox));
        assertEquals(true, PrimitiveType.CHAR.isAssignableBy(characterBox));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(longBox));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveType.CHAR.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(characterBox));
        assertEquals(true, PrimitiveType.BYTE.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(longBox));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveType.BYTE.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(characterBox));
        assertEquals(true, PrimitiveType.SHORT.isAssignableBy(byteBox));
        assertEquals(true, PrimitiveType.SHORT.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(longBox));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveType.SHORT.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveType.INT.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveType.INT.isAssignableBy(characterBox));
        assertEquals(true, PrimitiveType.INT.isAssignableBy(byteBox));
        assertEquals(true, PrimitiveType.INT.isAssignableBy(shortBox));
        assertEquals(true, PrimitiveType.INT.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveType.INT.isAssignableBy(longBox));
        assertEquals(false, PrimitiveType.INT.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveType.INT.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveType.LONG.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveType.LONG.isAssignableBy(characterBox));
        assertEquals(true, PrimitiveType.LONG.isAssignableBy(byteBox));
        assertEquals(true, PrimitiveType.LONG.isAssignableBy(shortBox));
        assertEquals(true, PrimitiveType.LONG.isAssignableBy(integerBox));
        assertEquals(true, PrimitiveType.LONG.isAssignableBy(longBox));
        assertEquals(false, PrimitiveType.LONG.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveType.LONG.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(characterBox));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(longBox));
        assertEquals(true, PrimitiveType.FLOAT.isAssignableBy(floatBox));
        assertEquals(false, PrimitiveType.FLOAT.isAssignableBy(doubleBox));

        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(booleanBox));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(characterBox));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(byteBox));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(shortBox));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(integerBox));
        assertEquals(false, PrimitiveType.DOUBLE.isAssignableBy(longBox));
        assertEquals(true, PrimitiveType.DOUBLE.isAssignableBy(floatBox));
        assertEquals(true, PrimitiveType.DOUBLE.isAssignableBy(doubleBox));
    }

    @Test
    public void testIsAssignableByAnythingElse() {
        for (PrimitiveType ptu : PrimitiveType.ALL) {
            assertEquals(false, ptu.isAssignableBy(OBJECT));
            assertEquals(false, ptu.isAssignableBy(STRING));
            assertEquals(false, ptu.isAssignableBy(NullType.INSTANCE));
            assertEquals(false, ptu.isAssignableBy(VoidType.INSTANCE));
            assertEquals(false, ptu.isAssignableBy(arrayOfBooleans));
            assertEquals(false, ptu.isAssignableBy(arrayOfListOfA));
        }
    }

}
