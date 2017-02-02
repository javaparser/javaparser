package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.Expression;
import org.junit.Test;

import static org.junit.Assert.*;

public class TreeStructureJsonCallbackTest {
    @Test
    public void testWithType() {
        StringBuilder stringBuilder = new StringBuilder();
        TreeStructureVisitor visitor = new TreeStructureVisitor(new TreeStructureJsonCallback(stringBuilder, true));
        Expression expression = JavaParser.parseExpression("x(1,1)");

        expression.accept(visitor, new Context());

        assertEquals("{\"root\":{\"type\":\"MethodCallExpr\",\"name\":{\"type\":\"SimpleName\",\"identifier\":\"x\"},\"arguments\":{\"type\":\"IntegerLiteralExpr\",\"value\":\"1\"},\"arguments\":{\"type\":\"IntegerLiteralExpr\",\"value\":\"1\"}}}", stringBuilder.toString());
    }

    @Test
    public void testWithoutType() {
        StringBuilder stringBuilder = new StringBuilder();
        TreeStructureVisitor visitor = new TreeStructureVisitor(new TreeStructureJsonCallback(stringBuilder, false));
        Expression expression = JavaParser.parseExpression("1+1");

        expression.accept(visitor, new Context());

        assertEquals("{\"root\":{\"operator\":\"PLUS\",\"left\":{\"value\":\"1\"},\"right\":{\"value\":\"1\"}}}", stringBuilder.toString());
    }
}