/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

package com.github.javaparser.generator.core.utils;

import static com.github.javaparser.generator.core.utils.CodeUtils.castValue;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import org.junit.jupiter.api.Test;

/**
 * Comprehensive tests for CodeUtils.
 * Verifies type casting logic for code generation.
 */
class CodeUtilsTest {

    private static final String RETURN_VALUE = "this";

    @Test
    void castReturnValue_whenAValueMatchesTheExpectedTypeNoCastIsNeeded() {
        Type returnType = PrimitiveType.booleanType();
        Type valueType = PrimitiveType.booleanType();

        assertEquals(RETURN_VALUE, castValue(RETURN_VALUE, returnType, valueType.asString()));
    }

    @Test
    void castReturnValue_whenAValueIsNotAssignedByReturnShouldBeCasted() {
        Type returnType = StaticJavaParser.parseType("String");
        Type valueType = StaticJavaParser.parseType("Object");

        assertEquals(
                String.format("(%s) %s", returnType, RETURN_VALUE),
                castValue(RETURN_VALUE, returnType, valueType.asString()));
    }

    @Test
    void testCastValue_WithPrimitiveTypes() {
        Type intType = PrimitiveType.intType();
        Type longType = StaticJavaParser.parseType("long");

        String result = castValue(RETURN_VALUE, longType, intType.asString());
        assertEquals(String.format("(%s) %s", "long", RETURN_VALUE), result);
    }

    @Test
    void testCastValue_WithSamePrimitiveTypes() {
        Type intType = PrimitiveType.intType();
        String result = castValue(RETURN_VALUE, intType, "int");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithWrapperTypes() {
        Type stringType = StaticJavaParser.parseType("String");
        Type objectType = StaticJavaParser.parseType("Object");

        String result = castValue(RETURN_VALUE, stringType, objectType.asString());
        assertEquals(String.format("(%s) %s", "String", RETURN_VALUE), result);
    }

    @Test
    void testCastValue_WithSameWrapperTypes() {
        Type stringType = StaticJavaParser.parseType("String");
        String result = castValue(RETURN_VALUE, stringType, "String");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithGenericTypes() {
        Type listType = StaticJavaParser.parseType("List<String>");
        Type objectType = StaticJavaParser.parseType("Object");

        String result = castValue(RETURN_VALUE, listType, objectType.asString());
        assertEquals(String.format("(%s) %s", "List<String>", RETURN_VALUE), result);
    }

    @Test
    void testCastValue_WithArrayTypes() {
        Type stringArrayType = StaticJavaParser.parseType("String[]");
        Type objectArrayType = StaticJavaParser.parseType("Object[]");

        String result = castValue(RETURN_VALUE, stringArrayType, objectArrayType.asString());
        assertEquals(String.format("(%s) %s", "String[]", RETURN_VALUE), result);
    }

    @Test
    void testCastValue_WithNestedGenericTypes() {
        Type mapType = StaticJavaParser.parseType("Map<String, List<Integer>>");
        Type objectType = StaticJavaParser.parseType("Object");

        String result = castValue(RETURN_VALUE, mapType, objectType.asString());
        assertEquals(String.format("(%s) %s", "Map<String, List<Integer>>", RETURN_VALUE), result);
    }

    @Test
    void testCastValue_WithWildcardTypes() {
        Type wildcardType = StaticJavaParser.parseType("List<? extends Number>");
        Type objectType = StaticJavaParser.parseType("Object");

        String result = castValue(RETURN_VALUE, wildcardType, objectType.asString());
        assertEquals(String.format("(%s) %s", "List<? extends Number>", RETURN_VALUE), result);
    }

    @Test
    void testCastValue_WithBooleanPrimitive() {
        Type booleanType = PrimitiveType.booleanType();
        String result = castValue(RETURN_VALUE, booleanType, "boolean");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithCharPrimitive() {
        Type charType = PrimitiveType.charType();
        String result = castValue(RETURN_VALUE, charType, "char");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithBytePrimitive() {
        Type byteType = PrimitiveType.byteType();
        String result = castValue(RETURN_VALUE, byteType, "byte");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithShortPrimitive() {
        Type shortType = PrimitiveType.shortType();
        String result = castValue(RETURN_VALUE, shortType, "short");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithLongPrimitive() {
        Type longType = PrimitiveType.longType();
        String result = castValue(RETURN_VALUE, longType, "long");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithFloatPrimitive() {
        Type floatType = PrimitiveType.floatType();
        String result = castValue(RETURN_VALUE, floatType, "float");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithDoublePrimitive() {
        Type doubleType = PrimitiveType.doubleType();
        String result = castValue(RETURN_VALUE, doubleType, "double");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithVoidType() {
        Type voidType = PrimitiveType.voidType();
        String result = castValue(RETURN_VALUE, voidType, "void");
        assertEquals(RETURN_VALUE, result);
    }

    @Test
    void testCastValue_WithDifferentValueString() {
        Type stringType = StaticJavaParser.parseType("String");
        String customValue = "customValue";
        String result = castValue(customValue, stringType, "String");
        assertEquals(customValue, result);
    }

    @Test
    void testCastValue_WithComplexTypeNames() {
        Type complexType = StaticJavaParser.parseType("com.example.package.ClassName");
        Type objectType = StaticJavaParser.parseType("Object");

        String result = castValue(RETURN_VALUE, complexType, objectType.asString());
        assertEquals(String.format("(%s) %s", "com.example.package.ClassName", RETURN_VALUE), result);
    }

    @Test
    void testCastValue_ReturnTypeNotNull() {
        Type returnType = StaticJavaParser.parseType("String");
        String result = castValue(RETURN_VALUE, returnType, "Object");
        assertNotNull(result);
    }

    @Test
    void testCastValue_WithNullValueString() {
        Type stringType = StaticJavaParser.parseType("String");
        String result = castValue(null, stringType, "String");
        assertEquals(null, result);
    }
}
