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
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import com.github.javaparser.printer.configuration.PrinterConfiguration;
import com.github.javaparser.utils.TestUtils;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.EXPRESSION;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_21_PREVIEW_INCOMPLETE;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

class Java21PreviewValidatorTest {

    private final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_21_PREVIEW_INCOMPLETE));

    /**
     * String templates available within Java 21 (Preview), Java 22 (Preview).
     */
    @Nested
    class PatternMatching {
        @Test
        void template() {
            ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider(
                    "STR.\"test\\{5+5}\""));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void textBlock() {
            ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider(
                    "STR.\"\"\"\ntest\\{5+5}\n\"\"\""));
            TestUtils.assertNoProblems(result);
        }

        @Test
        void serializeStringLiteral() {
            ParseResult<Expression> result = javaParser.parseExpression("STR.\"test\\{5+5}\"");
            TestUtils.assertNoProblems(result);

            PrinterConfiguration configuration = new DefaultPrinterConfiguration();
            String printed = new DefaultPrettyPrinter(configuration).print(result.getResult().get());

            assertEqualsStringIgnoringEol("STR.\"test\\{5+5}\"", printed);
        }

        @Test
        void serializeTextBlock() {
            ParseResult<Expression> result = javaParser.parseExpression("STR.\"\"\"\ntest\\{5+5}\n\"\"\"");
            TestUtils.assertNoProblems(result);

            PrinterConfiguration configuration = new DefaultPrinterConfiguration();
            String printed = new DefaultPrettyPrinter(configuration).print(result.getResult().get());

            assertEqualsStringIgnoringEol(
                    "STR.\"\"\"\n" +
                    "    test\\{5+5}\n" +
                    "    \"\"\"", printed);
        }

    }


}
