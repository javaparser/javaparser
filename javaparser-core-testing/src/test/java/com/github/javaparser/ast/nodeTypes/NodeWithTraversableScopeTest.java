package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.utils.TestUtils.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertFalse;

class NodeWithTraversableScopeTest {
    @Test
    void traverse1() {
        NodeWithTraversableScope expression = parseExpression("getAddress().name.startsWith(\"abc\")");

        assertInstanceOf(MethodCallExpr.class, expression);
        expression = (NodeWithTraversableScope) expression.traverseScope().get();
        assertInstanceOf(FieldAccessExpr.class, expression);
        expression = (NodeWithTraversableScope) expression.traverseScope().get();
        assertInstanceOf(MethodCallExpr.class, expression);
        assertFalse(expression.traverseScope().isPresent());
    }
}
