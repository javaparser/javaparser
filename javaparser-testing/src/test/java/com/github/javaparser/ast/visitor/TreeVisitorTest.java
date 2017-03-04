/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.ast.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TreeVisitorTest {
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

    @Test
    public void issue743ConcurrentModificationProblem() {
        Expression expression = JavaParser.parseExpression("new int[]{1,2,3,4}");

        StringBuilder result = new StringBuilder();
        TreeVisitor visitor = new TreeVisitor() {
            @Override
            public void process(Node node) {
                if (node instanceof IntegerLiteralExpr) {
                    node.getParentNode().ifPresent(
                            parent -> ((ArrayInitializerExpr) parent).getValues().add(new IntegerLiteralExpr("1")));
                }
                result.append("<").append(node).append("> ");
            }
        };
        visitor.visitPreOrder(expression);
        System.out.println(result);
    }

    @Test
    public void isValidPreOrderTraversal() {
        StringBuilder result = new StringBuilder();
        new TreeVisitor() {
            @Override
            public void process(Node node) {
                result.append("<").append(node).append("> ");
            }
        }.visitPreOrder(JavaParser.parseExpression("(2+3)+(4+5)"));
        assertEquals("<(2 + 3) + (4 + 5)> <(2 + 3)> <2 + 3> <2> <3> <(4 + 5)> <4 + 5> <4> <5> ", result.toString());
    }

    @Test
    public void isValidPostOrderTraversal() {
        StringBuilder result = new StringBuilder();
        new TreeVisitor() {
            @Override
            public void process(Node node) {
                result.append("<").append(node).append("> ");
            }
        }.visitPostOrder(JavaParser.parseExpression("(2+3)+(4+5)"));
        assertEquals("<2> <3> <2 + 3> <(2 + 3)> <4> <5> <4 + 5> <(4 + 5)> <(2 + 3) + (4 + 5)> ", result.toString());
    }

    @Test
    public void preOrderConcurrentModificationIsOk() {
        new TreeVisitor() {
            @Override
            public void process(Node node) {
                if (node instanceof IntegerLiteralExpr) {
                    node.getParentNode().ifPresent(
                            parent -> ((ArrayInitializerExpr) parent).getValues().add(new IntegerLiteralExpr("1")));
                }
            }
        }.visitPreOrder(JavaParser.parseExpression("new int[]{1,2,3,4}"));
    }

    @Test
    public void postOrderConcurrentModificationIsOk() {
        new TreeVisitor() {
            @Override
            public void process(Node node) {
                if (node instanceof IntegerLiteralExpr) {
                    node.getParentNode().ifPresent(
                            parent -> ((ArrayInitializerExpr) parent).getValues().add(new IntegerLiteralExpr("1")));
                }
            }
        }.visitPostOrder(JavaParser.parseExpression("new int[]{1,2,3,4}"));
    }
}
