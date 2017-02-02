package com.github.javaparser.ast.visitor.treestructure;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.Expression;
import org.junit.Test;

import static org.junit.Assert.*;

public class TreeStructureXmlCallbackTest {
    @Test
    public void test() {
        StringBuilder stringBuilder = new StringBuilder();
        TreeStructureVisitor visitor = new TreeStructureVisitor(new TreeStructureXmlCallback(stringBuilder, true));
        Expression expression = JavaParser.parseExpression("1+1");

        expression.accept(visitor, new Context());

        assertEquals("<root type='BinaryExpr' operator='PLUS'><left type='IntegerLiteralExpr' value='1'></left><right type='IntegerLiteralExpr' value='1'></right></root>", stringBuilder.toString());
    }
}