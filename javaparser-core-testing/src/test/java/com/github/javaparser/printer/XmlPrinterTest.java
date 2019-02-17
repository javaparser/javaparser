package com.github.javaparser.printer;

import com.github.javaparser.ast.expr.Expression;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static org.junit.jupiter.api.Assertions.assertEquals;

class XmlPrinterTest {
    @Test
    void testWithType() {
        Expression expression = parseExpression("1+1");
        XmlPrinter xmlOutput = new XmlPrinter(true);

        String output = xmlOutput.output(expression);

        assertEquals("<root type='BinaryExpr' operator='PLUS'><left type='IntegerLiteralExpr' value='1'></left><right type='IntegerLiteralExpr' value='1'></right></root>", output);
    }

    @Test
    void testWithoutType() {
        Expression expression = parseExpression("1+1");

        XmlPrinter xmlOutput = new XmlPrinter(false);

        String output = xmlOutput.output(expression);

        assertEquals("<root operator='PLUS'><left value='1'></left><right value='1'></right></root>", output);
    }

    @Test
    void testList() {
        Expression expression = parseExpression("a(1,2)");

        XmlPrinter xmlOutput = new XmlPrinter(true);

        String output = xmlOutput.output(expression);

        assertEquals("<root type='MethodCallExpr'><name type='SimpleName' identifier='a'></name><arguments><argument type='IntegerLiteralExpr' value='1'></argument><argument type='IntegerLiteralExpr' value='2'></argument></arguments></root>", output);
    }
}