/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.parseStatement;
import static java.util.Arrays.asList;
import static java.util.stream.Collectors.toList;
import static org.junit.jupiter.api.Assertions.assertEquals;

class TextBlockLiteralExprTest {
    @Test
    void htmlExample() {
        TextBlockLiteralExpr textBlock = parseStatement("String html = \"\"\"\n" +
                "              <html>\n" +
                "                  <body>\n" +
                "                      <p>Hello, world</p>\n" +
                "                  </body>\n" +
                "              </html>\n" +
                "              \"\"\";").findFirst(TextBlockLiteralExpr.class).get();

        assertEquals("              <html>\n" +
                "                  <body>\n" +
                "                      <p>Hello, world</p>\n" +
                "                  </body>\n" +
                "              </html>\n" +
                "              ", textBlock.getValue());

        assertEquals(asList(
                "<html>",
                "    <body>",
                "        <p>Hello, world</p>",
                "    </body>",
                "</html>",
                ""
        ), textBlock.stripIndentOfLines().collect(toList()));

        assertEquals("<html>\n" +
                "    <body>\n" +
                "        <p>Hello, world</p>\n" +
                "    </body>\n" +
                "</html>\n", textBlock.stripIndent());

        assertEquals("<html>\n" +
                "    <body>\n" +
                "        <p>Hello, world</p>\n" +
                "    </body>\n" +
                "</html>\n", textBlock.translateEscapes());
    }

    @Test
    void htmlExampleWithEndAllToTheLeft() {
        TextBlockLiteralExpr textBlock = parseStatement("String html = \"\"\"\n" +
                "              <html>\n" +
                "                  <body>\n" +
                "                      <p>Hello, world</p>\n" +
                "                  </body>\n" +
                "              </html>\n" +
                "\"\"\";").findFirst(TextBlockLiteralExpr.class).get();

        assertEquals(
                "              <html>\n" +
                        "                  <body>\n" +
                        "                      <p>Hello, world</p>\n" +
                        "                  </body>\n" +
                        "              </html>\n", textBlock.translateEscapes());
    }

    @Test
    void htmlExampleWithEndALittleToTheLeft() {
        TextBlockLiteralExpr textBlock = parseStatement("String html = \"\"\"\n" +
                "              <html>\n" +
                "                  <body>\n" +
                "                      <p>Hello, world</p>\n" +
                "                  </body>\n" +
                "              </html>\n" +
                "        \"\"\";").findFirst(TextBlockLiteralExpr.class).get();

        assertEquals("      <html>\n" +
                "          <body>\n" +
                "              <p>Hello, world</p>\n" +
                "          </body>\n" +
                "      </html>\n", textBlock.translateEscapes());
    }

    @Test
    void htmlExampleWithEndALittleToTheRight() {
        TextBlockLiteralExpr textBlock = parseStatement("String html = \"\"\"\n" +
                "              <html>\n" +
                "                  <body>\n" +
                "                      <p>Hello, world</p>\n" +
                "                  </body>\n" +
                "              </html>\n" +
                "                  \"\"\";").findFirst(TextBlockLiteralExpr.class).get();

        assertEquals("<html>\n" +
                "    <body>\n" +
                "        <p>Hello, world</p>\n" +
                "    </body>\n" +
                "</html>\n", textBlock.translateEscapes());
    }

    @Test
    void itIsLegalToUseDoubleQuoteFreelyInsideATextBlock() {
        parseStatement("String story = \"\"\"\n" +
                "    \"When I use a word,\" Humpty Dumpty said,\n" +
                "    in rather a scornful tone, \"it means just what I\n" +
                "    choose it to mean - neither more nor less.\"\n" +
                "    \"The question is,\" said Alice, \"whether you\n" +
                "    can make words mean so many different things.\"\n" +
                "    \"The question is,\" said Humpty Dumpty,\n" +
                "    \"which is to be master - that's all.\"\n" +
                "    \"\"\";");
    }

    @Test
    void sequencesOfThreeDoubleQuotesNeedAtLeastOneEscaped() {
        TextBlockLiteralExpr textBlock = parseStatement("String code = \n" +
                "    \"\"\"\n" +
                "    String text = \\\"\"\"\n" +
                "        A text block inside a text block\n" +
                "    \\\"\"\";\n" +
                "    \"\"\";").findFirst(TextBlockLiteralExpr.class).get();

        assertEquals("String text = \"\"\"\n" +
                "    A text block inside a text block\n" +
                "\"\"\";\n", textBlock.translateEscapes());
    }

    @Test
    void concatenatingTextBlocks() {
        parseStatement("String code = \"public void print(Object o) {\" +\n" +
                "              \"\"\"\n" +
                "                  System.out.println(Objects.toString(o));\n" +
                "              }\n" +
                "              \"\"\";");
    }

    @Test
    void forceTrailingWhitespace() {
        TextBlockLiteralExpr textBlock = parseStatement("String code = \"\"\"\n" +
                "The quick brown fox\\040\\040\n" +
                "jumps over the lazy dog\n" +
                "\"\"\";").findFirst(TextBlockLiteralExpr.class).get();

        assertEquals("The quick brown fox  \n" +
                "jumps over the lazy dog\n", textBlock.translateEscapes());
    }

    @Test
    void escapeLineTerminator() {
        TextBlockLiteralExpr textBlock = parseStatement("String text = \"\"\"\n" +
                "                Lorem ipsum dolor sit amet, consectetur adipiscing \\\n" +
                "                elit, sed do eiusmod tempor incididunt ut labore \\\n" +
                "                et dolore magna aliqua.\\\n" +
                "                \"\"\";").findFirst(TextBlockLiteralExpr.class).get();

        assertEquals("Lorem ipsum dolor sit amet, consectetur adipiscing " +
                "elit, sed do eiusmod tempor incididunt ut labore " +
                "et dolore magna aliqua.", textBlock.translateEscapes());
    }

    @Test
    void escapeSpace() {
        TextBlockLiteralExpr textBlock = parseStatement("String colors = \"\"\"\n" +
                "    red  \\s\n" +
                "    green\\s\n" +
                "    blue \\s\n" +
                "    \"\"\";").findFirst(TextBlockLiteralExpr.class).get();

        assertEquals("red   \n" +
                "green \n" +
                "blue  \n", textBlock.translateEscapes());
    }

    @Test
    void whiteSpaceLineShorterThanMiniumCommonPrefix() {
        TextBlockLiteralExpr textBlock = parseStatement("String text = \"\"\" \n" +
                "  Hello\n" +
                "  World\"\"\";").findFirst(TextBlockLiteralExpr.class).get();
        assertEquals("\nHello\n" +
                "World", textBlock.translateEscapes());
    }
}
