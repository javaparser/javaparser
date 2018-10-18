/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2018 The JavaParser Team.
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
package com.github.javaparser.serialization;

import com.github.javaparser.JavaParser;
import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.Type;
import org.junit.jupiter.api.Test;

import javax.json.Json;
import javax.json.JsonObject;
import javax.json.stream.JsonGenerator;

import java.io.StringReader;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import static com.github.javaparser.serialization.JavaParserJsonSerializerTest.*;
import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.normalizeEolInTextBlock;
import static org.junit.jupiter.api.Assertions.assertEquals;

class JavaParserJsonDeserializerTest {
    private final JavaParserJsonDeserializer deserializer = new JavaParserJsonDeserializer();

    @Test
    void simpleTest() {
        CompilationUnit cu = JavaParser.parse("public class X{} class Z{}");
        String serialized = serialize(cu, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("public class X {\n}\n\nclass Z {\n}\n", deserialized.toString());
        assertEquals(cu.hashCode(), deserialized.hashCode());
    }

    @Test
    void testRawType() {
        Type type = JavaParser.parseType("Blub");
        String serialized = serialize(type, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("Blub", deserialized.toString());
        assertEquals(type.hashCode(), deserialized.hashCode());
    }

    @Test
    void testDiamondType() {
        Type type = JavaParser.parseType("Blub<>");
        String serialized = serialize(type, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("Blub<>", deserialized.toString());
        assertEquals(type.hashCode(), deserialized.hashCode());
    }

    @Test
    void testGenerics() {
        Type type = JavaParser.parseType("Blub<Blab, Bleb>");
        String serialized = serialize(type, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("Blub<Blab, Bleb>", deserialized.toString());
        assertEquals(type.hashCode(), deserialized.hashCode());
    }

    @Test
    void testOperator() {
        Expression expr = JavaParser.parseExpression("1+1");
        String serialized = serialize(expr, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("1 + 1", deserialized.toString());
        assertEquals(expr.hashCode(), deserialized.hashCode());
    }

    @Test
    void testPrimitiveType() {
        Type type = JavaParser.parseType("int");
        String serialized = serialize(type, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("int", deserialized.toString());
        assertEquals(type.hashCode(), deserialized.hashCode());
    }

    @Test
    void testDelegate() {
        CompilationUnit cu = JavaParser.parse("public class X{} class Z{}");
        List<JavaParserJsonSerializer.Delegate> serializerDelegates = new LinkedList<>();
        JavaParserJsonSerializer.Delegate rangeSerializerDelegate = (node, generator) -> {
            if (node.getRange().isPresent()) {
                Range range = node.getRange().get();
                generator.writeStartObject("range");
                generator.write("beginLine", range.begin.line);
                generator.write("beginColumn", range.begin.column);
                generator.write("endLine", range.end.line);
                generator.write("endColumn", range.end.column);
                generator.writeEnd();
            }
        };
        serializerDelegates.add(rangeSerializerDelegate);
        String serialized = serialize(cu, false, serializerDelegates);

        Map<String, JavaParserJsonDeserializer.Delegate> deserializerDelegates = new HashMap<>();
        JavaParserJsonDeserializer.Delegate rangeDeserializerDelegate = (propertyName, jsonValue, node) -> {
            JsonObject jsonNode = (JsonObject)jsonValue;
            Position begin = new Position(jsonNode.getInt("beginLine"), jsonNode.getInt("beginColumn"));
            Position end = new Position(jsonNode.getInt("endLine"), jsonNode.getInt("endColumn"));
            node.setRange(new Range(begin, end));
        };
        deserializerDelegates.put("range", rangeDeserializerDelegate);

        Node deserialized = deserializer.deserializeObject(
                Json.createReader(new StringReader(serialized)),
                deserializerDelegates
        );
        Range range = deserialized.getRange().get();
        assertEquals(range.begin.line, 1);
        assertEquals(range.begin.line, 1);
        assertEquals(range.end.line, 1);
        assertEquals(range.end.column, 26);
    }

    /**
     * Assert that "actual" equals "expected", and that any EOL characters in "actual" are correct for the platform.
     */
    private static void assertEqualsNoEol(String expected, String actual) {
        assertEquals(normalizeEolInTextBlock(expected, EOL), actual);
    }

}
