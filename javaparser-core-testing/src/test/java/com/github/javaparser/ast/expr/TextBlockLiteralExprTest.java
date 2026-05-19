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

package com.github.javaparser.ast.expr;

import static com.github.javaparser.utils.TestParser.parseExpression;
import static com.github.javaparser.utils.TestParser.parseStatement;
import static java.util.Arrays.asList;
import static java.util.stream.Collectors.toList;
import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

class TextBlockLiteralExprTest {
    @Test
    void htmlExample() {
        TextBlockLiteralExpr textBlock = parseStatement("""
                        String html = ""\"
                                      <html>
                                          <body>
                                              <p>Hello, world</p>
                                          </body>
                                      </html>
                                      ""\";\
                        """)
                .findFirst(TextBlockLiteralExpr.class)
                .get();

        assertEquals(
                """
                              <html>
                                  <body>
                                      <p>Hello, world</p>
                                  </body>
                              </html>
                              """,
                textBlock.getValue());

        assertEquals(
                asList("<html>", "    <body>", "        <p>Hello, world</p>", "    </body>", "</html>", ""),
                textBlock.stripIndentOfLines().collect(toList()));

        assertEquals(
                """
                <html>
                    <body>
                        <p>Hello, world</p>
                    </body>
                </html>
                """,
                textBlock.stripIndent());

        assertEquals(
                """
                <html>
                    <body>
                        <p>Hello, world</p>
                    </body>
                </html>
                """,
                textBlock.translateEscapes());
    }

    @Test
    void htmlExampleWithEndAllToTheLeft() {
        TextBlockLiteralExpr textBlock = parseStatement("""
                        String html = ""\"
                                      <html>
                                          <body>
                                              <p>Hello, world</p>
                                          </body>
                                      </html>
                        ""\";\
                        """)
                .findFirst(TextBlockLiteralExpr.class)
                .get();

        assertEquals(
                """
                              <html>
                                  <body>
                                      <p>Hello, world</p>
                                  </body>
                              </html>
                """,
                textBlock.translateEscapes());
    }

    @Test
    void htmlExampleWithEndALittleToTheLeft() {
        TextBlockLiteralExpr textBlock = parseStatement("""
                        String html = ""\"
                                      <html>
                                          <body>
                                              <p>Hello, world</p>
                                          </body>
                                      </html>
                                ""\";\
                        """)
                .findFirst(TextBlockLiteralExpr.class)
                .get();

        assertEquals(
                """
                      <html>
                          <body>
                              <p>Hello, world</p>
                          </body>
                      </html>
                """,
                textBlock.translateEscapes());
    }

    @Test
    void htmlExampleWithEndALittleToTheRight() {
        TextBlockLiteralExpr textBlock = parseStatement("""
                        String html = ""\"
                                      <html>
                                          <body>
                                              <p>Hello, world</p>
                                          </body>
                                      </html>
                                          ""\";\
                        """)
                .findFirst(TextBlockLiteralExpr.class)
                .get();

        assertEquals(
                """
                <html>
                    <body>
                        <p>Hello, world</p>
                    </body>
                </html>
                """,
                textBlock.translateEscapes());
    }

    @Test
    void itIsLegalToUseDoubleQuoteFreelyInsideATextBlock() {
        parseStatement("""
                String story = ""\"
                    "When I use a word," Humpty Dumpty said,
                    in rather a scornful tone, "it means just what I
                    choose it to mean - neither more nor less."
                    "The question is," said Alice, "whether you
                    can make words mean so many different things."
                    "The question is," said Humpty Dumpty,
                    "which is to be master - that's all."
                    ""\";\
                """);
    }

    @Test
    void sequencesOfThreeDoubleQuotesNeedAtLeastOneEscaped() {
        TextBlockLiteralExpr textBlock = parseStatement("""
                        String code =\s
                            ""\"
                            String text = \\""\"
                                A text block inside a text block
                            \\""\";
                            ""\";\
                        """)
                .findFirst(TextBlockLiteralExpr.class)
                .get();

        assertEquals(
                """
                String text = ""\"
                    A text block inside a text block
                ""\";
                """,
                textBlock.translateEscapes());
    }

    @Test
    void concatenatingTextBlocks() {
        parseStatement("""
                String code = "public void print(Object o) {" +
                              ""\"
                                  System.out.println(Objects.toString(o));
                              }
                              ""\";\
                """);
    }

    @Test
    void forceTrailingWhitespace() {
        TextBlockLiteralExpr textBlock = parseStatement("""
                        String code = ""\"
                        The quick brown fox\\040\\040
                        jumps over the lazy dog
                        ""\";\
                        """)
                .findFirst(TextBlockLiteralExpr.class)
                .get();

        assertEquals("The quick brown fox  \n" + "jumps over the lazy dog\n", textBlock.translateEscapes());
    }

    @Test
    void escapeLineTerminator() {
        TextBlockLiteralExpr textBlock = parseStatement("""
                        String text = ""\"
                                        Lorem ipsum dolor sit amet, consectetur adipiscing \\
                                        elit, sed do eiusmod tempor incididunt ut labore \\
                                        et dolore magna aliqua.\\
                                        ""\";\
                        """)
                .findFirst(TextBlockLiteralExpr.class)
                .get();

        assertEquals(
                "Lorem ipsum dolor sit amet, consectetur adipiscing "
                        + "elit, sed do eiusmod tempor incididunt ut labore "
                        + "et dolore magna aliqua.",
                textBlock.translateEscapes());
    }

    @Test
    void escapeSpace() {
        TextBlockLiteralExpr textBlock = parseStatement("""
                        String colors = ""\"
                            red  \\s
                            green\\s
                            blue \\s
                            ""\";\
                        """)
                .findFirst(TextBlockLiteralExpr.class)
                .get();

        assertEquals("red   \n" + "green \n" + "blue  \n", textBlock.translateEscapes());
    }

    @Test
    void whiteSpaceLineShorterThanMiniumCommonPrefix() {
        TextBlockLiteralExpr textBlock = parseStatement("String text = \"\"\" \n" + "  Hello\n" + "  World\"\"\";")
                .findFirst(TextBlockLiteralExpr.class)
                .get();
        assertEquals("\nHello\n" + "World", textBlock.translateEscapes());
    }

    /**
     * Regression test for <a href="https://github.com/javaparser/javaparser/issues/4894">issue #4894</a>.
     * <p>
     * A text block whose last content characters before the closing {@code """} are an
     * escaped backslash ({@code \\}) on a separate line must parse successfully.
     */
    @Test
    void textBlockEndingInDoubleBackslashOnSeparateLineParses() {
        TextBlockLiteralExpr textBlock = parseExpression("\"\"\"\n" + "        foo\\\\\n" + "        \"\"\"");
        assertEquals("foo\\\n", textBlock.translateEscapes());
    }

    /**
     * Regression test for <a href="https://github.com/javaparser/javaparser/issues/4894">issue #4894</a>.
     * <p>
     * Canonical failing form: an escaped backslash ({@code \\}) sits immediately adjacent
     * to the closing {@code """} (no intervening newline)
     */
    @Test
    void textBlockEndingInDoubleBackslashAdjacentToCloserParses() {
        TextBlockLiteralExpr textBlock =
                parseExpression("\"\"\"\n" + "        arbitrary text\n" + "        \\\\\"\"\"");
        assertEquals("arbitrary text\n\\", textBlock.translateEscapes());
    }
}
