/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue3859Test extends AbstractResolutionTest {

    @Test
    void test() {
        String code = "import java.util.function.Consumer;\n" +
                "\n" +
                "class Demo {\n" +
                "    void foo(Consumer<String> arg) {}\n" +
                "    void print(Object arg) {}\n" +
                "    public void bar() {\n" +
                "        foo(s->print(s));\n" +
                "    }\n" +
                "    public void baz() {\n" +
                "        foo((s->print(s)));\n" +
                "    }\n" +
                "}\n";
        CompilationUnit cu = JavaParserAdapter.of(
                createParserWithResolver(defaultTypeSolver())).parse(code);

        List<LambdaExpr> lambdas = cu.findAll(LambdaExpr.class);
        assertEquals(2, lambdas.size());
        assertEquals("java.util.function.Consumer<java.lang.String>",
                lambdas.get(0).calculateResolvedType().describe());
        // Before the fix the following statement failed with an
        // `UnsupportedOperationException` because an extra `(...)` around
        // an argument wasn't handled.
        assertEquals("java.util.function.Consumer<java.lang.String>",
                lambdas.get(1).calculateResolvedType().describe());

        List<NameExpr> exprs = cu.findAll(NameExpr.class);
        assertEquals(2, exprs.size());
        assertEquals("? super java.lang.String",
                exprs.get(0).calculateResolvedType().describe());
        // Before the fix the following statement failed with an
        // `UnsupportedOperationException` because an extra `(...)` around
        // an argument wasn't handled.
        assertEquals("? super java.lang.String",
                exprs.get(1).calculateResolvedType().describe());
    }
}
