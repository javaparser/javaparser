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
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ArrayTypeTest {

    private ResolvedArrayType arrayOfBooleans;
    private ResolvedArrayType arrayOfStrings;
    private ResolvedArrayType arrayOfListOfA;
    private ResolvedArrayType arrayOfListOfStrings;
    private ReferenceTypeImpl OBJECT;
    private ReferenceTypeImpl STRING;
    private TypeSolver typeSolver;
    private ResolvedTypeParameterDeclaration tpA;

    @Before
    public void setup() {
        typeSolver = new ReflectionTypeSolver();
        OBJECT = new ReferenceTypeImpl(new ReflectionClassDeclaration(Object.class, typeSolver), typeSolver);
        STRING = new ReferenceTypeImpl(new ReflectionClassDeclaration(String.class, typeSolver), typeSolver);
        arrayOfBooleans = new ResolvedArrayType(ResolvedPrimitiveType.BOOLEAN);
        arrayOfStrings = new ResolvedArrayType(STRING);
        tpA = ResolvedTypeParameterDeclaration.onType("A", "foo.Bar", Collections.emptyList());
        arrayOfListOfA = new ResolvedArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(new ResolvedTypeVariable(tpA)), typeSolver));
        arrayOfListOfStrings = new ResolvedArrayType(new ReferenceTypeImpl(
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
        assertTrue(arrayOfBooleans == arrayOfBooleans.replaceTypeVariables(tpA, OBJECT));
        assertTrue(arrayOfStrings == arrayOfStrings.replaceTypeVariables(tpA, OBJECT));
        assertEquals(arrayOfListOfStrings, arrayOfListOfStrings.replaceTypeVariables(tpA, OBJECT));
        ResolvedArrayType arrayOfListOfObjects = new ResolvedArrayType(new ReferenceTypeImpl(
                new ReflectionInterfaceDeclaration(List.class, typeSolver),
                ImmutableList.of(OBJECT), typeSolver));
        assertEquals(true, arrayOfListOfA.replaceTypeVariables(tpA, OBJECT).isArray());
        assertEquals(ImmutableList.of(OBJECT),
                arrayOfListOfA.replaceTypeVariables(tpA, OBJECT).asArrayType().getComponentType()
                        .asReferenceType().typeParametersValues());
        assertEquals(new ReflectionInterfaceDeclaration(List.class, typeSolver),
                arrayOfListOfA.replaceTypeVariables(tpA, OBJECT).asArrayType().getComponentType()
                        .asReferenceType().getTypeDeclaration());
        assertEquals(new ReferenceTypeImpl(
                        new ReflectionInterfaceDeclaration(List.class, typeSolver),
                        ImmutableList.of(OBJECT), typeSolver),
                arrayOfListOfA.replaceTypeVariables(tpA, OBJECT).asArrayType().getComponentType());
        assertEquals(arrayOfListOfObjects, arrayOfListOfA.replaceTypeVariables(tpA, OBJECT));
        assertEquals(arrayOfListOfStrings, arrayOfListOfA.replaceTypeVariables(tpA, STRING));
        assertTrue(arrayOfListOfA != arrayOfListOfA.replaceTypeVariables(tpA, OBJECT));
    }

    @Test
    public void testIsAssignableBy() {
        assertEquals(false, arrayOfBooleans.isAssignableBy(OBJECT));
        assertEquals(false, arrayOfBooleans.isAssignableBy(STRING));
        assertEquals(false, arrayOfBooleans.isAssignableBy(ResolvedPrimitiveType.BOOLEAN));
        assertEquals(false, arrayOfBooleans.isAssignableBy(ResolvedVoidType.INSTANCE));

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
