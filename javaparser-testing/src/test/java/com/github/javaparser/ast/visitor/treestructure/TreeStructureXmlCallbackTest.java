package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.Expression;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TreeStructureXmlCallbackTest {
    @Test
    public void testWithType() {
        Expression expression = JavaParser.parseExpression("1+1");
        XmlDump xmlOutput = new XmlDump(true);

        String output = xmlOutput.output(expression);

        assertEquals("<root type='BinaryExpr' operator='PLUS'><left type='IntegerLiteralExpr' value='1'></left><right type='IntegerLiteralExpr' value='1'></right></root>", output);
    }

    @Test
    public void testWithoutType() {
        Expression expression = JavaParser.parseExpression("1+1");

        XmlDump xmlOutput = new XmlDump(false);

        String output = xmlOutput.output(expression);

        assertEquals("<root operator='PLUS'><left value='1'></left><right value='1'></right></root>", output);
    }

    @Test
    public void testList() {
        Expression expression = JavaParser.parseExpression("a(1,2)");

        XmlDump xmlOutput = new XmlDump(true);

        String output = xmlOutput.output(expression);

        assertEquals("<root type='MethodCallExpr'><name type='SimpleName' identifier='a'></name><arguments><argument type='IntegerLiteralExpr' value='1'></argument><argument type='IntegerLiteralExpr' value='2'></argument></arguments></root>", output);
    }
}