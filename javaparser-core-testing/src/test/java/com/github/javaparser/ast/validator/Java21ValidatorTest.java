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

package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultConfigurationOption;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.STATEMENT;
import static com.github.javaparser.ParseStart.VARIABLE_DECLARATION_EXPR;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_18;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_21_INCOMPLETE;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.StaticJavaParser.parseStatement;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

class Java21ValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_21_INCOMPLETE));

    /**
     * Pattern matching for switch available within Java 17 (Preview), Java 18 (Preview), Java 19 (Preview), Java 20 (Preview), Java 21 (Release).
     */
    @Nested
    class PatternMatching {
        @Test
        void simple() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider(
                    "switch (obj) {\n" +
                            "        case Integer i -> String.format(\"int %d\", i);\n" +
                            "        case Long l    -> String.format(\"long %d\", l);\n" +
                            "        case Double d  -> String.format(\"double %f\", d);\n" +
                            "        case String s  -> String.format(\"String %s\", s);\n" +
                            "        default        -> obj.toString();\n" +
                            "}"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void mixed() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider(
                    "switch (s) {\n" +
                            "        case null         -> System.out.println(\"Oops\");\n" +
                            "        case \"Foo\", \"Bar\" -> System.out.println(\"Great\");\n" +
                            "        default           -> System.out.println(\"Ok\");\n" +
                            "}"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void when() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider(
                    "switch (i) {\n" +
                            "    case Integer j when j > 0 -> {}\n" +
                            "}"));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void mixedWhen() {
            ParseResult<Statement> result = javaParser.parse(STATEMENT, provider(
                    "switch (i) {\n" +
                            "    case -1, 1 -> {}\n" +
                            "    case Integer j when j > 0 -> {}\n" +
                            "    case Integer j -> {}\n" +
                            "}"));
                    TestUtils.assertNoProblems(result);
        }

        @Test
        void serializeSwitch() {
            ParseResult<Statement> result = javaParser.parseStatement(
                    "switch (i) {\n" +
                    "    case -1, 1 -> {}\n" +
                    "    case Integer j when j > 0 -> {}\n" +
                    "    case Integer j -> {}\n" +
                    "}");
            TestUtils.assertNoProblems(result);

            PrinterConfiguration configuration = new DefaultPrinterConfiguration();
            String printed = new DefaultPrettyPrinter(configuration).print(result.getResult().get());

            assertEqualsStringIgnoringEol("switch(i) {\n" +
                    "    case -1, 1 ->\n" +
                    "        {\n" +
                    "        }\n" +
                    "    case Integer j when j > 0 ->\n" +
                    "        {\n" +
                    "        }\n" +
                    "    case Integer j ->\n" +
                    "        {\n" +
                    "        }\n" +
                    "}", printed);
        }

    }

}
