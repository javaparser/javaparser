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
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.javadoc.Javadoc;
import com.github.javaparser.javadoc.JavadocBlockTag;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.resolution.types.ResolvedType;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import javax.json.Json;
import java.io.StringReader;

import static com.github.javaparser.StaticJavaParser.*;
import static com.github.javaparser.serialization.JavaParserJsonSerializerTest.serialize;
import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.normalizeEolInTextBlock;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JavaParserJsonDeserializerTest {
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

    @Test
    void testOperator() {
        Expression expr = parseExpression("1+1");
        String serialized = serialize(expr, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("1 + 1", deserialized.toString());
        assertEquals(expr.hashCode(), deserialized.hashCode());
    }

    @Test
    void testPrimitiveType() {
        Type type = parseType("int");
        String serialized = serialize(type, false);

        Node deserialized = deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertEqualsNoEol("int", deserialized.toString());
        assertEquals(type.hashCode(), deserialized.hashCode());
    }

    @Test
    void testComment() {
        CompilationUnit cu = parse("/* block comment */\npublic class X{ \n // line comment\npublic void test() {}\n}");
        String serialized = serialize(cu, false);

        CompilationUnit deserialized = (CompilationUnit) deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));
        ClassOrInterfaceDeclaration classXDeclaration = deserialized.getClassByName("X").get();
        assertTrue(classXDeclaration.getComment().isPresent());

        Comment comment = classXDeclaration.getComment().get();
        assertEquals("com.github.javaparser.ast.comments.BlockComment", comment.getClass().getName());
        assertEquals(" block comment ", comment.getContent());

        MethodDeclaration methodDeclaration = classXDeclaration.getMethods().get(0);
        assertTrue(methodDeclaration.getComment().isPresent());
        assertEquals("com.github.javaparser.ast.comments.LineComment", methodDeclaration.getComment().get().getClass().getName());
        assertEquals(" line comment", methodDeclaration.getComment().get().getContent());
    }

    @Test
    void testJavaDocComment() {
        CompilationUnit cu = parse("public class X{ " +
                "     /**\n" +
                "     * Woke text.\n" +
                "     * @param a blub\n" +
                "     * @return true \n" +
                "     */" +
                "     public boolean test(int a) { return true; }\n" +
                "}");
        String serialized = serialize(cu, false);

        CompilationUnit deserialized = (CompilationUnit) deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));
        ClassOrInterfaceDeclaration classDeclaration = deserialized.getClassByName("X").get();
        MethodDeclaration methodDeclaration = classDeclaration.getMethods().get(0);
        assertTrue(methodDeclaration.getJavadoc().isPresent());
        Javadoc javadoc = methodDeclaration.getJavadoc().get();

        JavadocBlockTag paramBlockTag = javadoc.getBlockTags().get(0);
        assertEquals("param", paramBlockTag.getTagName());
        assertEquals("blub", paramBlockTag.getContent().toText());

        JavadocBlockTag returnBlockTag = javadoc.getBlockTags().get(1);
        assertEquals("return", returnBlockTag.getTagName());
        assertEquals("true", returnBlockTag.getContent().toText());
    }

    @Test
    void testNonMetaProperties() {
        CompilationUnit cu = parse("public class X{} class Z{}");
        String serialized = serialize(cu, false);

        CompilationUnit deserialized = (CompilationUnit) deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));

        assertTrue(deserialized.getRange().isPresent());
        Range range = deserialized.getRange().get();
        assertEquals(1, range.begin.line);
        assertEquals(1, range.begin.line);
        assertEquals(26, range.end.column);

        assertTrue(deserialized.getTokenRange().isPresent());
        TokenRange tokenRange = deserialized.getTokenRange().get();
        assertEquals("public", tokenRange.getBegin().getText());
        assertEquals("", tokenRange.getEnd().getText());
    }

    @Test
    void testAttachingSymbolResolver() {
        SymbolResolver stubResolver = new SymbolResolver() {
            @Override
            public <T> T resolveDeclaration(Node node, Class<T> resultClass) {
                return null;
            }

            @Override
            public <T> T toResolvedType(Type javaparserType, Class<T> resultClass) {
                return null;
            }

            @Override
            public ResolvedType calculateType(Expression expression) {
                return null;
            }
        };
        StaticJavaParser.getConfiguration().setSymbolResolver(stubResolver);
        CompilationUnit cu = parse("public class X{} class Z{}");
        String serialized = serialize(cu, false);

        CompilationUnit deserialized = (CompilationUnit) deserializer.deserializeObject(Json.createReader(new StringReader(serialized)));
        assertTrue(deserialized.containsData(Node.SYMBOL_RESOLVER_KEY));
        assertEquals(stubResolver, deserialized.getData(Node.SYMBOL_RESOLVER_KEY));
    }

    @AfterAll
    static void clearConfiguration() {
        StaticJavaParser.setConfiguration(new ParserConfiguration());
    }

    /**
     * Assert that "actual" equals "expected", and that any EOL characters in "actual" are correct for the platform.
     */
    private static void assertEqualsNoEol(String expected, String actual) {
        assertEquals(normalizeEolInTextBlock(expected, EOL), actual);
    }

}
