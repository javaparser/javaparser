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

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import org.junit.jupiter.api.Test;

public class Issue4188Test extends AbstractResolutionTest {

    @Test
    public void test() {

        String code = "import java.util.Optional;\n"
                + "\n"
                + "public class MethodInvocation {\n"
                + "\n"
                + "    // Resolves successfully\n"
                + "    public void staticMethodInvocation(Foo foo) {\n"
                + "        Optional<Integer> priority = Optional.of(4);\n"
                + "        priority.map(Foo::staticConvert).orElse(\"0\");\n"
                + "    }\n"
                + "\n"
                + "    // Does not resolve\n"
                + "    public void instanceMethodInvocation(Foo foo) {\n"
                + "        Optional<Integer> priority = Optional.of(4);\n"
                + "        priority.map(foo::convert).orElse(\"0\");\n"
                + "    }\n"
                + "\n"
                + "    // Does not resolve\n"
                + "    public void defaultMethodInvocation(Bar bar) {\n"
                + "        Optional<Integer> priority = Optional.of(4);\n"
                + "        priority.map(bar::convert).orElse(\"0\");\n"
                + "    }\n"
                + "\n"
                + "    public static class Foo {\n"
                + "        public String convert(int priority) {\n"
                + "            return Integer.toString(priority);\n"
                + "        }\n"
                + "\n"
                + "        public static String staticConvert(int priority) {\n"
                + "            return Integer.toString(priority);\n"
                + "        }\n"
                + "    }\n"
                + "\n"
                + "    public interface Bar {\n"
                + "        default String convert(int priority) {\n"
                + "            return Integer.toString(priority);\n"
                + "        }\n"
                + "    }\n"
                + "}";
        JavaParser parser = createParserWithResolver(defaultTypeSolver());
        CompilationUnit cu = parser.parse(code).getResult().get();
        cu.findAll(MethodCallExpr.class).forEach(MethodCallExpr::resolve);
    }
}
