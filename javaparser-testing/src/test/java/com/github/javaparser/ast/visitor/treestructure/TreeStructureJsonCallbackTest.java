package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.Expression;
import org.junit.Test;

import static org.junit.Assert.*;

public class TreeStructureJsonCallbackTest {
    @Test
    public void testWithType() {
        JsonDump jsonDump = new JsonDump(true);
        Expression expression = JavaParser.parseExpression("x(1,1)");

        String output = jsonDump.output(expression);

        assertEquals("{\"type\":\"MethodCallExpr\",\"name\":{\"type\":\"SimpleName\",\"identifier\":\"x\"},\"arguments\":[{\"type\":\"IntegerLiteralExpr\",\"value\":\"1\"},{\"type\":\"IntegerLiteralExpr\",\"value\":\"1\"}]}", output);
    }

    @Test
    public void testWithoutType() {
        JsonDump jsonDump = new JsonDump(false);
        Expression expression = JavaParser.parseExpression("1+1");

        String output = jsonDump.output(expression);

        assertEquals("{\"operator\":\"PLUS\",\"left\":{\"value\":\"1\"},\"right\":{\"value\":\"1\"}}", output);
    }
}