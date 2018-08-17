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

import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.SimpleName;
import org.junit.Test;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static org.junit.Assert.assertEquals;

public class TreeVisitorTest implements JavaParserSugar {
    @Override
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        return new JavaParser(new ParserConfiguration().setLanguageLevel(BLEEDING_EDGE)).parse(start, provider);
    }

    @Test
    public void isValidBreadthFirstTraversal() {
        Expression expression = parseExpression("(2+3)+(4+5)");

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
        Expression expression = parseExpression("new int[]{1,2,3,4}");

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
        }.visitPreOrder(parseExpression("(2+3)+(4+5)"));
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
        }.visitPostOrder(parseExpression("(2+3)+(4+5)"));
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
        }.visitPreOrder(parseExpression("new int[]{1,2,3,4}"));
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
        }.visitPostOrder(parseExpression("new int[]{1,2,3,4}"));
    }

    @Test
    public void parents() {
        CompilationUnit cu = parse("class X{int x=1;}");
        SimpleName x = cu.getClassByName("X").get().getMember(0).asFieldDeclaration().getVariable(0).getName();

        Node.ParentsVisitor visitor = new Node.ParentsVisitor(x);
        assertEquals("x = 1", visitor.next().toString());
        assertEquals("int x = 1;", visitor.next().toString());
        assertEqualsNoEol("class X {\n" +
                "\n" +
                "    int x = 1;\n" +
                "}", visitor.next().toString());
        assertEqualsNoEol("class X {\n" +
                "\n" +
                "    int x = 1;\n" +
                "}\n", visitor.next().toString());
        assertEquals(false, visitor.hasNext());
    }

    @Test
    public void isValidDirectChildrenTraversal() {
        Expression expression = parseExpression("(2+3)+(4+5)");

        StringBuilder result = new StringBuilder();

        TreeVisitor visitor = new TreeVisitor() {
            @Override
            public void process(Node node) {
                result.append("<").append(node).append("> ");
            }
        };

        visitor.visitDirectChildren(expression);
        assertEquals("<(2 + 3)> <(4 + 5)> ", result.toString());
    }
}
