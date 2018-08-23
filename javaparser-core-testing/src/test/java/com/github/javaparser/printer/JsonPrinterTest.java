package com.github.javaparser.printer;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.Expression;
import org.junit.Test;

import static com.github.javaparser.JavaParser.*;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.Assert.*;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.io.BufferedWriter;

public class JsonPrinterTest {
    @Test
    public void testWithType() {
        JsonPrinter jsonPrinter = new JsonPrinter(true);
        Expression expression = parseExpression("x(1,1)");

        String output = jsonPrinter.output(expression);

        assertEquals("{\"_type\":\"MethodCallExpr\",\"name\":{\"_type\":\"SimpleName\",\"identifier\":\"x\"},\"arguments\":[{\"_type\":\"IntegerLiteralExpr\",\"value\":\"1\"},{\"_type\":\"IntegerLiteralExpr\",\"value\":\"1\"}]}", output);
    }

    @Test
    public void testWithoutType() {
        JsonPrinter jsonPrinter = new JsonPrinter(false);
        Expression expression = parseExpression("1+1");

        String output = jsonPrinter.output(expression);

        assertEquals("{\"operator\":\"PLUS\",\"left\":{\"value\":\"1\"},\"right\":{\"value\":\"1\"}}", output);
    }

    @Test
    public void testEscaping() {
        JsonPrinter jsonPrinter = new JsonPrinter(false);
        CompilationUnit expression = parse("class X {//hi\"" + EOL + "int x;}");

        String output = jsonPrinter.output(expression);

        assertEquals("{\"types\":[{\"isInterface\":\"false\",\"name\":{\"identifier\":\"X\",\"comment\":{\"content\":\"hi\\\"\"}},\"members\":[{\"variables\":[{\"name\":{\"identifier\":\"x\"},\"type\":{\"type\":\"INT\"}}]}]}]}", output);
    }

    @Test
    public void issue1338() {
        String code = "class Test {" +
                "  public void method() {" +
                "    String.format(\"I'm using %s\", \"JavaParser\");" +
                "  }" +
                "}";
        CompilationUnit unit = parse(code);
        JsonPrinter printer = new JsonPrinter(true);
        printer.output(unit);
    }

    @Test
    public void issue1421() {
        // Handle multi-line strings in JSON output
        String code = "/* \n" +
                "* Some comment\n" +
                "*/\n" +
                "public class Test {}";
        CompilationUnit unit = parse(code);
        JsonPrinter printer = new JsonPrinter(true);

        String output = printer.output(unit);

        assertEquals("{\"_type\":\"CompilationUnit\",\"types\":[{\"_type\":\"ClassOrInterfaceDeclaration\",\"modifiers\":[\"public\"],\"isInterface\":\"false\",\"name\":{\"_type\":\"SimpleName\",\"identifier\":\"Test\"},\"comment\":{\"_type\":\"BlockComment\",\"content\":\" \\n* Some comment\\n\"}}]}", output);
    }
}