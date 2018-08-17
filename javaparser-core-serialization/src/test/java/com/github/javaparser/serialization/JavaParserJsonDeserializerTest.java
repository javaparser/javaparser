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

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.type.Type;
import org.junit.jupiter.api.Test;

import javax.json.Json;

import java.io.StringReader;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static com.github.javaparser.serialization.JavaParserJsonSerializerTest.*;
import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.normalizeEolInTextBlock;
import static org.junit.jupiter.api.Assertions.assertEquals;

class JavaParserJsonDeserializerTest implements JavaParserSugar {
    @Override
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE)).parse(start, provider);
    }

    private final JavaParserJsonDeserializer deserializer = new JavaParserJsonDeserializer();

    @Test
    void simpleTest() {
        CompilationUnit cu = parse("public class X{} class Z{}");
        String serialized = serialize(cu, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("public class X {\n}\n\nclass Z {\n}\n", deserialized.toString());
        assertEquals(cu.hashCode(), deserialized.hashCode());
    }

    @Test
    void testRawType() {
        Type type = parseType("Blub");
        String serialized = serialize(type, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("Blub", deserialized.toString());
        assertEquals(type.hashCode(), deserialized.hashCode());
    }

    @Test
    void testDiamondType() {
        Type type = parseType("Blub<>");
        String serialized = serialize(type, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("Blub<>", deserialized.toString());
        assertEquals(type.hashCode(), deserialized.hashCode());
    }

    @Test
    void testGenerics() {
        Type type = parseType("Blub<Blab, Bleb>");
        String serialized = serialize(type, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("Blub<Blab, Bleb>", deserialized.toString());
        assertEquals(type.hashCode(), deserialized.hashCode());
    }

    /**
     * Assert that "actual" equals "expected", and that any EOL characters in "actual" are correct for the platform.
     */
    private static void assertEqualsNoEol(String expected, String actual) {
        assertEquals(normalizeEolInTextBlock(expected, EOL), actual);
    }

}
