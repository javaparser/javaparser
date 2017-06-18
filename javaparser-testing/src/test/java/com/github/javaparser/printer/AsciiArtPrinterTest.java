package com.github.javaparser.printer;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.printer.AsciiArtPrinter;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class AsciiArtPrinterTest {
    @Test
    public void test() {
        AsciiArtPrinter dump = new AsciiArtPrinter();
        Expression expression = JavaParser.parseExpression("1+a(1,1)");

        String output = dump.output(expression);

        assertEquals("root (BinaryExpr)\n" +
                "\toperator: PLUS\n" +
                "\tleft (IntegerLiteralExpr)\n" +
                "\t\tvalue: 1\n" +
                "\tright (MethodCallExpr)\n" +
                "\t\tname (SimpleName)\n" +
                "\t\t\tidentifier: a\n" +
                "\t\targuments (IntegerLiteralExpr)\n" +
                "\t\t\tvalue: 1\n" +
                "\t\targuments (IntegerLiteralExpr)\n" +
                "\t\t\tvalue: 1\n", output);
    }
}