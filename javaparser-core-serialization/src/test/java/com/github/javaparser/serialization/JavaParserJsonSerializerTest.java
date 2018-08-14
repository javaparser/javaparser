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
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import org.junit.jupiter.api.Test;

import javax.json.Json;
import javax.json.stream.JsonGenerator;
import javax.json.stream.JsonGeneratorFactory;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

class JavaParserJsonSerializerTest {
    @Test
    void test() {
        CompilationUnit cu = JavaParser.parse("class X{java.util.Y y;}");

        String serialized = serialize(cu, false);

        assertEquals("{\"!\":\"com.github.javaparser.ast.CompilationUnit\",\"imports\":[],\"types\":[{\"!\":\"com.github.javaparser.ast.body.ClassOrInterfaceDeclaration\",\"extendedTypes\":[],\"implementedTypes\":[],\"isInterface\":\"false\",\"typeParameters\":[],\"members\":[{\"!\":\"com.github.javaparser.ast.body.FieldDeclaration\",\"modifiers\":[],\"variables\":[{\"!\":\"com.github.javaparser.ast.body.VariableDeclarator\",\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"y\"},\"type\":{\"!\":\"com.github.javaparser.ast.type.ClassOrInterfaceType\",\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"Y\"},\"scope\":{\"!\":\"com.github.javaparser.ast.type.ClassOrInterfaceType\",\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"util\"},\"scope\":{\"!\":\"com.github.javaparser.ast.type.ClassOrInterfaceType\",\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"java\"},\"annotations\":[]},\"annotations\":[]},\"annotations\":[]}}],\"annotations\":[]}],\"modifiers\":[],\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"X\"},\"annotations\":[]}]}", serialized);
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
