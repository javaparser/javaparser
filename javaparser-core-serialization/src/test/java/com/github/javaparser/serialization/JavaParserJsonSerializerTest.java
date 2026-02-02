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
package com.github.javaparser.serialization;

import static com.github.javaparser.StaticJavaParser.parse;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.google.common.truth.Truth;
import jakarta.json.Json;
import jakarta.json.stream.JsonGenerator;
import jakarta.json.stream.JsonGeneratorFactory;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.Map;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

class JavaParserJsonSerializerTest {
    @Test
    void test() throws IOException {
        CompilationUnit cu = parse("class X{java.util.Y y;}");
        String serialized = serialize(cu, true);

        InputStream is = getClass().getResourceAsStream("/example.json");
        byte[] buffer = new byte[1024 * 1024];
        int len = is.read(buffer);
        Assumptions.assumeTrue(len > 0);
        String expected = new String(buffer, 0, len);
        System.out.println(serialized);
        Truth.assertThat(serialized).isEqualTo(expected);
    }

    static String serialize(Node node, boolean prettyPrint) {
        Map<String, ?> config = new HashMap<>();
        if (prettyPrint) {
            config.put(JsonGenerator.PRETTY_PRINTING, null);
        }
        JsonGeneratorFactory generatorFactory = Json.createGeneratorFactory(config);
        JavaParserJsonSerializer serializer = new JavaParserJsonSerializer();
        StringWriter jsonWriter = new StringWriter();
        try (JsonGenerator generator = generatorFactory.createGenerator(jsonWriter)) {
            serializer.serialize(node, generator);
        }
        return jsonWriter.toString();
    }
}
