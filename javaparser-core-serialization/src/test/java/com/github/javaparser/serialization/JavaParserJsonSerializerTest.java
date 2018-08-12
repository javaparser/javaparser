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

        assertEquals("{\"!\":\"com.github.javaparser.ast.CompilationUnit\",\"types\":[{\"!\":\"com.github.javaparser.ast.body.ClassOrInterfaceDeclaration\",\"isInterface\":\"false\",\"members\":[{\"!\":\"com.github.javaparser.ast.body.FieldDeclaration\",\"variables\":[{\"!\":\"com.github.javaparser.ast.body.VariableDeclarator\",\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"y\"},\"type\":{\"!\":\"com.github.javaparser.ast.type.ClassOrInterfaceType\",\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"Y\"},\"scope\":{\"!\":\"com.github.javaparser.ast.type.ClassOrInterfaceType\",\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"util\"},\"scope\":{\"!\":\"com.github.javaparser.ast.type.ClassOrInterfaceType\",\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"java\"}}}}}]}],\"name\":{\"!\":\"com.github.javaparser.ast.expr.SimpleName\",\"identifier\":\"X\"}}]}", serialized);
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
