/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import org.junit.jupiter.api.Test;

public class Issue4488Test {
    @Test
    void cannotChangeMethodNameInLambda() {
        ParserConfiguration parserConfiguration = new ParserConfiguration();
        parserConfiguration.setLexicalPreservationEnabled(true);
        StaticJavaParser.setConfiguration(parserConfiguration);

        CompilationUnit cu =
                StaticJavaParser.parse("class Test {\n" + "	private Map<String, String> dummyMap = new HashMap<>();\n"
                        + "	public String dummyFunction(String name) {\n"
                        + "		return dummyMap.computeIfAbsent(name,\n"
                        + "			(Function<String, String>) s -> SomeFunction.withAMethodHere(\"test\").build());\n"
                        + "	}\n"
                        + "}");

        cu.accept(
                new ModifierVisitor() {
                    @Override
                    public Visitable visit(MethodCallExpr mc, Object arg) {
                        if (mc.getNameAsString().equals("withAMethodHere")) {
                            return mc.setName("replacedMethodHere");
                        }
                        return super.visit(mc, arg);
                    }
                },
                null);

        assertEquals(
                "class Test {\n" + "	private Map<String, String> dummyMap = new HashMap<>();\n"
                        + "	public String dummyFunction(String name) {\n"
                        + "		return dummyMap.computeIfAbsent(name,\n"
                        + "			(Function<String, String>) s -> SomeFunction.replacedMethodHere(\"test\").build());\n"
                        + "	}\n"
                        + "}",
                LexicalPreservingPrinter.print(cu));
    }
}
