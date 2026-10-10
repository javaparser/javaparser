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

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

/**
 * Object is a supertype of every interface (JLS 4.10.2), so the least upper bound of an interface and a type that
 * does not implement it is Object.
 */
class Issue5158Test extends AbstractSymbolResolutionTest {

    private static CompilationUnit parse(String code) {
        ParserConfiguration configuration = new ParserConfiguration()
                .setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_17)
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        return new JavaParser(configuration).parse(code).getResult().get();
    }

    @Test
    void switchExpressionOfAnInterfaceAndAClass() {
        CompilationUnit cu = parse("import java.util.HashMap;\n"
                + "import java.util.Map;\n"
                + "class Test {\n"
                + "    Object m(int i) {\n"
                + "        Map<String, String> map = new HashMap<>();\n"
                + "        Object o = switch (i) {\n"
                + "            case 0 -> map;\n"
                + "            default -> Integer.valueOf(i);\n"
                + "        };\n"
                + "        return o;\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();

        assertEquals("java.lang.Object", switchExpr.calculateResolvedType().describe());
    }

    @Test
    void switchExpressionOfTwoUnrelatedInterfaces() {
        CompilationUnit cu = parse("import java.util.Map;\n"
                + "class Test {\n"
                + "    Object m(int i, Map<String, String> map, Runnable runnable) {\n"
                + "        return switch (i) {\n"
                + "            case 0 -> map;\n"
                + "            default -> runnable;\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();

        assertEquals("java.lang.Object", switchExpr.calculateResolvedType().describe());
    }

    @Test
    void conditionalExpressionOfAnInterfaceAndAClass() {
        CompilationUnit cu = parse("import java.util.Map;\n"
                + "class Test {\n"
                + "    Object m(boolean b, Map<String, String> map) {\n"
                + "        return b ? map : Integer.valueOf(0);\n"
                + "    }\n"
                + "}");

        ConditionalExpr conditionalExpr = cu.findFirst(ConditionalExpr.class).get();

        assertEquals("java.lang.Object", conditionalExpr.calculateResolvedType().describe());
    }

    @Test
    void switchExpressionOfAClassAndAnInterfaceSharingAnInterface() {
        // Object must not hide the shared interface
        CompilationUnit cu = parse("import java.util.ArrayList;\n"
                + "class Test {\n"
                + "    Object m(int i, ArrayList<String> list) {\n"
                + "        return switch (i) {\n"
                + "            case 0 -> list;\n"
                + "            default -> Integer.valueOf(i);\n"
                + "        };\n"
                + "    }\n"
                + "}");

        SwitchExpr switchExpr = cu.findFirst(SwitchExpr.class).get();

        assertEquals("java.io.Serializable", switchExpr.calculateResolvedType().describe());
    }
}
