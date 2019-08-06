package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.utils.TestParser;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestParser.*;
import static org.junit.jupiter.api.Assertions.*;

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
    }
}