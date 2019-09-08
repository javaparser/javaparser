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

import com.github.javaparser.resolution.declarations.ResolvedTypeParameterDeclaration;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedTypeVariable;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionClassDeclaration;
import com.github.javaparser.symbolsolver.reflectionmodel.ReflectionInterfaceDeclaration;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertThrows;

class VoidTypeTest {

    private ResolvedArrayType arrayOfBooleans;
    private ResolvedArrayType arrayOfListOfA;
    private ReferenceTypeImpl OBJECT;
    private ReferenceTypeImpl STRING;
    private TypeSolver typeSolver;

    @BeforeEach
    void setup() {
        typeSolver = new ReflectionTypeSolver();
        OBJECT = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ResolvedArrayType(ResolvedPrimitiveType.BOOLEAN);
        arrayOfListOfA = new ResolvedArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ResolvedTypeVariable(ResolvedTypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList()))), typeSolver));
    }

    @Test
    void testIsArray() {
        assertEquals(false, ResolvedVoidType.INSTANCE.isArray());
    }

    @Test
    void testIsPrimitive() {
        assertEquals(false, ResolvedVoidType.INSTANCE.isPrimitive());
    }

    @Test
    void testIsNull() {
        assertEquals(false, ResolvedVoidType.INSTANCE.isNull());
    }

    @Test
    void testIsReference() {
        assertEquals(false, ResolvedVoidType.INSTANCE.isReference());
    }

    @Test
    void testIsReferenceType() {
        assertEquals(false, ResolvedVoidType.INSTANCE.isReferenceType());
    }

    @Test
    void testIsVoid() {
        assertEquals(true, ResolvedVoidType.INSTANCE.isVoid());
    }

    @Test
    void testIsTypeVariable() {
        assertEquals(false, ResolvedVoidType.INSTANCE.isTypeVariable());
    }

    @Test
    void testAsReferenceTypeUsage() {
        assertThrows(UnsupportedOperationException.class, () -> ResolvedVoidType.INSTANCE.asReferenceType());
    }

    @Test
    void testAsTypeParameter() {
        assertThrows(UnsupportedOperationException.class, () -> ResolvedVoidType.INSTANCE.asTypeParameter());
    }

    @Test
    void testAsArrayTypeUsage() {
        assertThrows(UnsupportedOperationException.class, () -> ResolvedVoidType.INSTANCE.asArrayType());
    }

    @Test
    void testAsDescribe() {
        assertEquals("void", ResolvedVoidType.INSTANCE.describe());
    }

    @Test
    void testIsAssignableBy() {
        try {
            assertEquals(false, ResolvedVoidType.INSTANCE.isAssignableBy(NullType.INSTANCE));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, ResolvedVoidType.INSTANCE.isAssignableBy(OBJECT));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, ResolvedVoidType.INSTANCE.isAssignableBy(STRING));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, ResolvedVoidType.INSTANCE.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
            fail();
        } catch (UnsupportedOperationException e) {

        }
        try {
            assertEquals(false, ResolvedVoidType.INSTANCE.isAssignableBy(ResolvedVoidType.INSTANCE));
            fail();
        } catch (UnsupportedOperationException e) {

        }
    }

}
