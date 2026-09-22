/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

package com.github.javaparser.ast.validator;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_16;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.validator.Java1_1ValidatorTest.allModifiers;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.stmt.LocalEnumDeclarationStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import java.util.concurrent.atomic.AtomicBoolean;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

class Java16ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_16));

    @Test
    void localInterface() {
        ParseResult<CompilationUnit> result =
                javaParser.parse(COMPILATION_UNIT, provider("class X{ void x() {" + "interface I{}}}"));
        assertNoProblems(result);
    }

    @Test
    void localEnum() {
        ParseResult<CompilationUnit> result =
                javaParser.parse(COMPILATION_UNIT, provider("class X{ void x() {enum E{A,B}}}"));
        assertNoProblems(result);

        CompilationUnit cu = result.getResult().get();
        LocalEnumDeclarationStmt localEnumStmt =
                cu.findFirst(LocalEnumDeclarationStmt.class).get();
        assertTrue(localEnumStmt.isLocalEnumDeclarationStmt());
        assertSame(localEnumStmt, localEnumStmt.asLocalEnumDeclarationStmt());
        assertSame(JavaParserMetaModel.localEnumDeclarationStmtMetaModel, localEnumStmt.getMetaModel());

        AtomicBoolean consumerCalled = new AtomicBoolean(false);
        localEnumStmt.ifLocalEnumDeclarationStmt(s -> consumerCalled.set(true));
        assertTrue(consumerCalled.get());
        assertSame(localEnumStmt, localEnumStmt.toLocalEnumDeclarationStmt().get());

        EnumDeclaration enumDeclaration = localEnumStmt.getEnumDeclaration();
        assertEquals("E", enumDeclaration.getNameAsString());
        assertEquals("A", enumDeclaration.getEntry(0).getNameAsString());
        assertEquals("B", enumDeclaration.getEntry(1).getNameAsString());
        assertSame(localEnumStmt, enumDeclaration.getParentNode().get());
        assertTrue(enumDeclaration.isLocalEnumDeclaration());
        assertFalse(enumDeclaration.getFullyQualifiedName().isPresent());

        // setEnumDeclaration is a no-op when given the node it already holds
        localEnumStmt.setEnumDeclaration(enumDeclaration);
        assertSame(enumDeclaration, localEnumStmt.getEnumDeclaration());

        LocalEnumDeclarationStmt cloned = localEnumStmt.clone();
        assertEquals(localEnumStmt, cloned);

        LocalEnumDeclarationStmt differentEnumDeclaration =
                new LocalEnumDeclarationStmt(new EnumDeclaration().setName("Other"));
        assertNotEquals(localEnumStmt, differentEnumDeclaration);

        LocalEnumDeclarationStmt differentComment = cloned.clone();
        differentComment.setComment(new LineComment("different"));
        assertNotEquals(localEnumStmt, differentComment);

        ParseResult<Statement> reprinted = javaParser.parse(STATEMENT, provider(cloned.toString()));
        assertNoProblems(reprinted);
        assertEquals(cloned, reprinted.getResult().get());

        EnumDeclaration replacement = new EnumDeclaration().setName("F");
        assertTrue(localEnumStmt.replace(enumDeclaration, replacement));
        assertSame(replacement, localEnumStmt.getEnumDeclaration());
        assertFalse(localEnumStmt.replace(null, replacement));
        assertFalse(localEnumStmt.replace(new EnumDeclaration(), replacement));

        LocalEnumDeclarationStmt viaAllFieldsConstructor = new LocalEnumDeclarationStmt(replacement.clone());
        assertEquals("F", viaAllFieldsConstructor.getEnumDeclaration().getNameAsString());
    }

    @Test
    void localEnumWithImplements() {
        ParseResult<CompilationUnit> result = javaParser.parse(
                COMPILATION_UNIT, provider("class X{ void x() {enum E implements Comparable<E> {A,B}}}"));
        assertNoProblems(result);

        LocalEnumDeclarationStmt localEnumStmt = result.getResult()
                .get()
                .findFirst(LocalEnumDeclarationStmt.class)
                .get();
        assertEquals(
                "Comparable",
                localEnumStmt.getEnumDeclaration().getImplementedTypes(0).getNameAsString());
    }

    @Test
    void nonLocalEnumStatementRejectsLocalEnumCasters() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider(";"));
        assertNoProblems(result);
        Statement emptyStmt = result.getResult().get();

        assertFalse(emptyStmt.isLocalEnumDeclarationStmt());
        assertThrows(IllegalStateException.class, emptyStmt::asLocalEnumDeclarationStmt);
        assertFalse(emptyStmt.toLocalEnumDeclarationStmt().isPresent());

        AtomicBoolean consumerCalled = new AtomicBoolean(false);
        emptyStmt.ifLocalEnumDeclarationStmt(s -> consumerCalled.set(true));
        assertFalse(consumerCalled.get());
    }

    /**
     * A statement beginning with `enum` used as an identifier must still stay parsable, and must
     * yield the clean {@code ReservedKeywordValidator} message instead of a raw JavaCC parse
     * error. The local-enum-declaration lookahead in BlockStatement() must not greedily commit
     * these to EnumDeclaration().
     */
    @Test
    void enumUsedAsIdentifierYieldsCleanMessageInsteadOfParseError() {
        assertProblems(
                javaParser.parse(STATEMENT, provider("enum = 3;")),
                "(line 1,col 1) 'enum' cannot be used as an identifier as it is a keyword.");
        assertProblems(
                javaParser.parse(STATEMENT, provider("enum.foo();")),
                "(line 1,col 1) 'enum' cannot be used as an identifier as it is a keyword.");
        assertProblems(
                javaParser.parse(STATEMENT, provider("enum x = null;")),
                "(line 1,col 1) 'enum' cannot be used as an identifier as it is a keyword.");
        assertProblems(
                javaParser.parse(STATEMENT, provider("enum[0] = 1;")),
                "(line 1,col 1) 'enum' cannot be used as an identifier as it is a keyword.");
        assertProblems(
                javaParser.parse(STATEMENT, provider("enum++;")),
                "(line 1,col 1) 'enum' cannot be used as an identifier as it is a keyword.");
    }

    @Test
    void localEnumModifiers() {
        ParseResult<CompilationUnit> result =
                javaParser.parse(COMPILATION_UNIT, provider("class X{ void x() {" + allModifiers + "enum E{A,B}}}"));
        assertProblems(
                result,
                "(line 1,col 20) Can have only one of 'public', 'protected', 'private'.",
                "(line 1,col 20) Can have only one of 'final', 'abstract'.",
                "(line 1,col 20) Can have only one of 'native', 'strictfp'.",
                "(line 1,col 20) 'public' is not allowed here.",
                "(line 1,col 20) 'protected' is not allowed here.",
                "(line 1,col 20) 'private' is not allowed here.",
                "(line 1,col 20) 'abstract' is not allowed here.",
                "(line 1,col 20) 'static' is not allowed here.",
                "(line 1,col 20) 'final' is not allowed here.",
                "(line 1,col 20) 'transient' is not allowed here.",
                "(line 1,col 20) 'volatile' is not allowed here.",
                "(line 1,col 20) 'synchronized' is not allowed here.",
                "(line 1,col 20) 'native' is not allowed here.",
                "(line 1,col 20) 'transitive' is not allowed here.",
                "(line 1,col 20) 'default' is not allowed here.");
    }

    @Nested
    class Yield {
        @Test
        void yieldAllowed() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3: yield 6;}"));
            assertNoProblems(result);
        }
    }

    @Nested
    class PatternMatching {
        @Test
        void patternMatchingAllowed() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("if (a instanceof String s) {}"));
            assertNoProblems(result);
        }

        @Test
        void recordPatternsForbidden() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("if (a instanceof Box(String s)) {}"));
            assertProblems(
                    result,
                    "(line 1,col 18) Record patterns are not supported. Pay attention that this feature is supported starting from 'JAVA_21' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.");
        }
    }

    /**
     * Records are available within Java 14 (preview), Java 15 (2nd preview), and Java 16 (release).
     * The introduction of records means that they are no longer able to be used as identifiers.
     */
    @Nested
    class Record {

        @Nested
        class RecordAsTypeIdentifierForbidden {
            @Test
            void recordUsedAsClassIdentifier() {
                String s = "public class record {}";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                assertProblems(
                        result,
                        "(line 1,col 14) 'record' is a restricted identifier and cannot be used for type declarations");
            }

            @Test
            void recordUsedAsEnumIdentifier() {
                String s = "public enum record {}";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                assertProblems(
                        result,
                        "(line 1,col 13) 'record' is a restricted identifier and cannot be used for type declarations");
            }

            @Test
            void recordUsedAsRecordIdentifier() {
                String s = "public record record() {}";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                assertProblems(
                        result,
                        "(line 1,col 15) 'record' is a restricted identifier and cannot be used for type declarations");
            }
        }

        @Nested
        class RecordUsedAsIdentifierAllowedAsFieldDeclarations {
            @Test
            void recordUsedAsFieldIdentifierInClass() {
                String s = "class X { int record; }";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                assertNoProblems(result);
            }

            @Test
            void recordUsedAsFieldIdentifierInInterface() {
                String s = "interface X { int record; }";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                assertNoProblems(result);
            }
        }

        @Nested
        class RecordDeclarationPermitted {
            @Test
            void recordDeclaration() {
                String s = "record X() { }";
                ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider(s));
                assertNoProblems(result);
            }
        }
    }
}
