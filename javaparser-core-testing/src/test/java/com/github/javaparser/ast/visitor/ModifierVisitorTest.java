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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseBodyDeclaration;
import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.utils.Utils.EOL;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

class ModifierVisitorTest {
    @Test
    void makeSureParentListsCanBeModified() {
        NodeList<StringLiteralExpr> list = new NodeList<>();
        list.add(new StringLiteralExpr("t"));
        list.add(new StringLiteralExpr("a"));
        list.add(new StringLiteralExpr("b"));
        list.add(new StringLiteralExpr("c"));

        list.accept(new ModifierVisitor<Void>() {
            @Override
            public Visitable visit(final StringLiteralExpr n, final Void arg) {
                String v = n.getValue();

                list.addFirst(new StringLiteralExpr("extra " + v));
                list.remove(new StringLiteralExpr("t"));

                if (v.equals("a")) {
                    return new StringLiteralExpr("x");
                }
                if (v.equals("b")) {
                    return null;
                }

                return n;
            }
        }, null);

        assertEquals("extra c", list.get(0).getValue());
        assertEquals("extra b", list.get(1).getValue());
        assertEquals("extra a", list.get(2).getValue());
        assertEquals("extra t", list.get(3).getValue());
        assertEquals("x", list.get(4).getValue());
        assertEquals("c", list.get(5).getValue());
        assertEquals(6, list.size());
    }

    @Test
    void binaryExprReturnsLeftExpressionWhenRightSideIsRemoved() {
        Expression expression = parseExpression("1+2");
        Visitable result = expression.accept(new ModifierVisitor<Void>() {
            public Visitable visit(IntegerLiteralExpr integerLiteralExpr, Void arg) {
                if (integerLiteralExpr.getValue().equals("1")) {
                    return null;
                }
                return integerLiteralExpr;
            }
        }, null);
        assertEquals("2", result.toString());
    }

    @Test
    void binaryExprReturnsRightExpressionWhenLeftSideIsRemoved() {
        final Expression expression = parseExpression("1+2");
        final Visitable result = expression.accept(new ModifierVisitor<Void>() {
            public Visitable visit(IntegerLiteralExpr integerLiteralExpr, Void arg) {
                if (integerLiteralExpr.getValue().equals("2")) {
                    return null;
                }
                return integerLiteralExpr;
            }
        }, null);
        assertEquals("1", result.toString());
    }

    @Test
    void fieldDeclarationCantSurviveWithoutVariables() {
        final BodyDeclaration<?> bodyDeclaration = parseBodyDeclaration("int x=1;");

        final Visitable result = bodyDeclaration.accept(new ModifierVisitor<Void>() {
            public Visitable visit(VariableDeclarator x, Void arg) {
                return null;
            }
        }, null);

        assertNull(result);
    }

    @Test
    void variableDeclarationCantSurviveWithoutVariables() {
        final BodyDeclaration<?> bodyDeclaration = parseBodyDeclaration("void x() {int x=1;}");

        final Visitable result = bodyDeclaration.accept(new ModifierVisitor<Void>() {
            public Visitable visit(VariableDeclarator x, Void arg) {
                return null;
            }
        }, null);

        assertEquals("void x() {" + EOL + "}", result.toString());
    }

    @Test
    void issue2124() {
        ModifierVisitor<Void> modifier = new ModifierVisitor<>();
        CompilationUnit cu = StaticJavaParser.parse("\n" +
                "public class ModifierVisitorTest {\n" +
                "    private void causesException() {\n" +
                "        String[] listWithExtraCommaAndEqualElements = {\"a\", \"a\",};\n" +
                "    }\n" +
                "}");
        LexicalPreservingPrinter.setup(cu);
        cu.accept(modifier, null);
        System.out.println(LexicalPreservingPrinter.print(cu));
    }
}
