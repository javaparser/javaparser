package com.github.javaparser.ast.junit.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.TreeVisitor;
import org.junit.Test;

import static org.junit.Assert.*;

public class TreeVisitorTest {
    @Test
    public void depthFirst() {
        Expression expression = JavaParser.parseExpression("(2+3)+(4+5)");

        StringBuilder result = new StringBuilder();

        TreeVisitor visitor = new TreeVisitor() {
            @Override
            public void process(Node node) {
                result.append("<").append(node).append("> ");
            }
        };

        visitor.visitDepthFirst(expression);
        assertEquals("<(2 + 3) + (4 + 5)> <(2 + 3)> <2 + 3> <2> <3> <(4 + 5)> <4 + 5> <4> <5> ", result.toString());
    }

    @Test
    public void breadthFirst() {
        Expression expression = JavaParser.parseExpression("(2+3)+(4+5)");

        StringBuilder result = new StringBuilder();

        TreeVisitor visitor = new TreeVisitor() {
            @Override
            public void process(Node node) {
                result.append("<").append(node).append("> ");
            }
        };

        visitor.visitBreadthFirst(expression);
        assertEquals("<(2 + 3) + (4 + 5)> <(2 + 3)> <(4 + 5)> <2 + 3> <4 + 5> <2> <3> <4> <5> ", result.toString());
    }
}