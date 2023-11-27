/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.symbolsolver.model.typesystem;

import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class PrimitiveTypeTest {

    private ResolvedArrayType arrayOfBooleans;
    private ResolvedArrayType arrayOfListOfA;
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

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
        OBJECT = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver));
        STRING = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver));
        arrayOfBooleans = new ResolvedArrayType(ResolvedPrimitiveType.BOOLEAN);
        arrayOfListOfA = new ResolvedArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ResolvedTypeVariable(ResolvedTypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList())))));

        booleanBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Boolean.class, typeSolver));
        characterBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Character.class, typeSolver));
        byteBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Byte.class, typeSolver));
        shortBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Short.class, typeSolver));
        integerBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Integer.class, typeSolver));
        longBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Long.class, typeSolver));
        floatBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Float.class, typeSolver));
        doubleBox = new ReferenceTypeImpl(new ReflectionClassDeclaration(Double.class, typeSolver));

    }

    @Test
    void testIsArray() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            assertEquals(false, ptu.isArray());
        }
    }

    @Test
    void testIsPrimitive() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            assertEquals(true, ptu.isPrimitive());
        }
    }

    @Test
    void testIsNull() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            assertEquals(false, ptu.isNull());
        }
    }

    @Test
    void testIsReference() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            assertEquals(false, ptu.isReference());
        }
    }

    @Test
    void testIsReferenceType() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            assertEquals(false, ptu.isReferenceType());
        }
    }

    @Test
    void testIsVoid() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            assertEquals(false, ptu.isVoid());
        }
    }

    @Test
    void testIsTypeVariable() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            assertEquals(false, ptu.isTypeVariable());
        }
    }

    @Test
    void testAsReferenceTypeUsage() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            try {
                ptu.asReferenceType();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    void testAsTypeParameter() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            try {
                ptu.asTypeParameter();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    void testAsArrayTypeUsage() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            try {
                ptu.asArrayType();
                fail();
            } catch (UnsupportedOperationException e) {
            }
        }
    }

    @Test
    void testAsDescribe() {
        assertEquals("boolean", ResolvedPrimitiveType.BOOLEAN.describe());
        assertEquals("char", ResolvedPrimitiveType.CHAR.describe());
        assertEquals("byte", ResolvedPrimitiveType.BYTE.describe());
        assertEquals("short", ResolvedPrimitiveType.SHORT.describe());
        assertEquals("int", ResolvedPrimitiveType.INT.describe());
        assertEquals("long", ResolvedPrimitiveType.LONG.describe());
        assertEquals("float", ResolvedPrimitiveType.FLOAT.describe());
        assertEquals("double", ResolvedPrimitiveType.DOUBLE.describe());
    }

    @Test
    void testIsAssignableByOtherPrimitiveTypes() {
        assertEquals(true, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(ResolvedPrimitiveType.DOUBLE));

        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(true, ResolvedPrimitiveType.CHAR.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(ResolvedPrimitiveType.DOUBLE));

        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(true, ResolvedPrimitiveType.BYTE.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(ResolvedPrimitiveType.DOUBLE));

        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(true, ResolvedPrimitiveType.SHORT.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(true, ResolvedPrimitiveType.SHORT.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(ResolvedPrimitiveType.DOUBLE));

        assertEquals(false, ResolvedPrimitiveType.INT.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(true, ResolvedPrimitiveType.INT.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(true, ResolvedPrimitiveType.INT.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(true, ResolvedPrimitiveType.INT.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(true, ResolvedPrimitiveType.INT.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(false, ResolvedPrimitiveType.INT.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(false, ResolvedPrimitiveType.INT.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, ResolvedPrimitiveType.INT.isAssignableBy(ResolvedPrimitiveType.DOUBLE));

        assertEquals(false, ResolvedPrimitiveType.LONG.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(false, ResolvedPrimitiveType.LONG.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, ResolvedPrimitiveType.LONG.isAssignableBy(ResolvedPrimitiveType.DOUBLE));

        assertEquals(false, ResolvedPrimitiveType.FLOAT.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(false, ResolvedPrimitiveType.FLOAT.isAssignableBy(ResolvedPrimitiveType.DOUBLE));

        assertEquals(false, ResolvedPrimitiveType.DOUBLE.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(ResolvedPrimitiveType.CHAR));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(ResolvedPrimitiveType.BYTE));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(ResolvedPrimitiveType.SHORT));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(ResolvedPrimitiveType.INT));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(ResolvedPrimitiveType.LONG));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(ResolvedPrimitiveType.FLOAT));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(ResolvedPrimitiveType.DOUBLE));
    }

    @Test
    void testIsAssignableByBoxedTypes() {
        assertEquals(true, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(booleanBox));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(characterBox));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(byteBox));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(shortBox));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(integerBox));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(longBox));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(floatBox));
        assertEquals(false, ResolvedPrimitiveType.BOOLEAN.isAssignableBy(doubleBox));

        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(booleanBox));
        assertEquals(true, ResolvedPrimitiveType.CHAR.isAssignableBy(characterBox));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(byteBox));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(shortBox));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(integerBox));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(longBox));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(floatBox));
        assertEquals(false, ResolvedPrimitiveType.CHAR.isAssignableBy(doubleBox));

        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(booleanBox));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(characterBox));
        assertEquals(true, ResolvedPrimitiveType.BYTE.isAssignableBy(byteBox));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(shortBox));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(integerBox));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(longBox));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(floatBox));
        assertEquals(false, ResolvedPrimitiveType.BYTE.isAssignableBy(doubleBox));

        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(booleanBox));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(characterBox));
        assertEquals(true, ResolvedPrimitiveType.SHORT.isAssignableBy(byteBox));
        assertEquals(true, ResolvedPrimitiveType.SHORT.isAssignableBy(shortBox));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(integerBox));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(longBox));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(floatBox));
        assertEquals(false, ResolvedPrimitiveType.SHORT.isAssignableBy(doubleBox));

        assertEquals(false, ResolvedPrimitiveType.INT.isAssignableBy(booleanBox));
        assertEquals(true, ResolvedPrimitiveType.INT.isAssignableBy(characterBox));
        assertEquals(true, ResolvedPrimitiveType.INT.isAssignableBy(byteBox));
        assertEquals(true, ResolvedPrimitiveType.INT.isAssignableBy(shortBox));
        assertEquals(true, ResolvedPrimitiveType.INT.isAssignableBy(integerBox));
        assertEquals(false, ResolvedPrimitiveType.INT.isAssignableBy(longBox));
        assertEquals(false, ResolvedPrimitiveType.INT.isAssignableBy(floatBox));
        assertEquals(false, ResolvedPrimitiveType.INT.isAssignableBy(doubleBox));

        assertEquals(false, ResolvedPrimitiveType.LONG.isAssignableBy(booleanBox));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(characterBox));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(byteBox));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(shortBox));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(integerBox));
        assertEquals(true, ResolvedPrimitiveType.LONG.isAssignableBy(longBox));
        assertEquals(false, ResolvedPrimitiveType.LONG.isAssignableBy(floatBox));
        assertEquals(false, ResolvedPrimitiveType.LONG.isAssignableBy(doubleBox));

        assertEquals(false, ResolvedPrimitiveType.FLOAT.isAssignableBy(booleanBox));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(characterBox));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(byteBox));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(shortBox));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(integerBox));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(longBox));
        assertEquals(true, ResolvedPrimitiveType.FLOAT.isAssignableBy(floatBox));
        assertEquals(false, ResolvedPrimitiveType.FLOAT.isAssignableBy(doubleBox));

        assertEquals(false, ResolvedPrimitiveType.DOUBLE.isAssignableBy(booleanBox));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(characterBox));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(byteBox));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(shortBox));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(integerBox));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(longBox));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(floatBox));
        assertEquals(true, ResolvedPrimitiveType.DOUBLE.isAssignableBy(doubleBox));
    }

    @Test
    void testIsAssignableByAnythingElse() {
        for (ResolvedPrimitiveType ptu : ResolvedPrimitiveType.values()) {
            assertEquals(false, ptu.isAssignableBy(OBJECT));
            assertEquals(false, ptu.isAssignableBy(STRING));
            assertEquals(false, ptu.isAssignableBy(NullType.INSTANCE));
            assertEquals(false, ptu.isAssignableBy(ResolvedVoidType.INSTANCE));
            assertEquals(false, ptu.isAssignableBy(arrayOfBooleans));
            assertEquals(false, ptu.isAssignableBy(arrayOfListOfA));
        }
    }
    
    @Test
    void testIsNumeric() {
    	assertFalse(ResolvedPrimitiveType.BOOLEAN.isNumeric());
    	assertTrue(ResolvedPrimitiveType.CHAR.isNumeric());
    	assertTrue(ResolvedPrimitiveType.BYTE.isNumeric());
    	assertTrue(ResolvedPrimitiveType.SHORT.isNumeric());
    	assertTrue(ResolvedPrimitiveType.INT.isNumeric());
    	assertTrue(ResolvedPrimitiveType.LONG.isNumeric());
    	assertTrue(ResolvedPrimitiveType.FLOAT.isNumeric());
    	assertTrue(ResolvedPrimitiveType.DOUBLE.isNumeric());
    }

}
