package com.github.javaparser.ast.expr;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseStart;
import com.github.javaparser.ParserConfiguration;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseExpression;
import static com.github.javaparser.Providers.provider;
import static org.junit.Assert.assertEquals;

public class CharLiteralExprTest {
    @Test
    public void parseSimpleChar() {
        CharLiteralExpr c = parseExpression("'a'");
        assertEquals("a", c.getValue());
    }

    @Test
    public void parseSimpleEscape() {
        CharLiteralExpr c = parseExpression("'\\t'");
        assertEquals("\\t", c.getValue());
    }

    @Test
    public void parseUnicode() {
        CharLiteralExpr c = parseExpression("'Ω'");
        assertEquals("Ω", c.getValue());
    }

    @Test
    public void parseNumericEscape() {
        CharLiteralExpr c = parseExpression("'\\177'");
        assertEquals("\\177", c.getValue());
    }

    @Test
    public void parseUnicodeEscape() {
        CharLiteralExpr c = parseExpression("'\\u03a9'");
        assertEquals("\\u03a9", c.getValue());
    }

    @Test
    public void parseUnicodeEscapedEscape() {
        JavaParser javaParser = new JavaParser(new ParserConfiguration()
                .setPreprocessUnicodeEscapes(true));

        CharLiteralExpr c = javaParser.parse(ParseStart.EXPRESSION, provider("'\\u005c''")).getResult().get().asCharLiteralExpr();
        assertEquals("\\'", c.getValue());
    }
}
