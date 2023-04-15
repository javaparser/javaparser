/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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


import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue2406Test extends AbstractSymbolResolutionTest {

    @Test
    public void test() {

        ParserConfiguration config = new ParserConfiguration()
                .setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        String s = "import java.lang.reflect.Array;\n" +
                "\n" +
                "public class Main {\n" +
                "    public static <T, U> T[] copyOf(U[] original, int newLength, Class<? extends T[]> newType) {\n" +
                "        @SuppressWarnings(\"unchecked\")\n" +
                "        T[] copy = ((Object) newType == (Object)Object[].class)\n" +
                "            ? (T[]) new Object[newLength]\n" +
                "            : (T[]) Array.newInstance(newType.getComponentType(), newLength);\n" +
                "        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));\n" +
                "        return copy;\n" +
                "    }\n" +
                "\n" +
                "    public static void main(String[] args) {\n" +
                "        String[] source = {\"a\", \"b\", \"c\"};\n" +
                "        String[] target = copyOf(source, 2, source.getClass());\n" +
                "        for (String e : target) System.out.println(e);\n" +
                "    }\n" +
                "}";
        CompilationUnit cu = StaticJavaParser.parse(s);
        List<MethodCallExpr> mces = cu.findAll(MethodCallExpr.class, new Predicate() {

            @Override
            public boolean test(Object t) {
                return ((MethodCallExpr)t).getNameAsString().equals("copyOf");
            }
            
        });
        
        assertEquals("Main.copyOf(U[], int, java.lang.Class<? extends T[]>)", mces.get(0).resolve().getQualifiedSignature());

    }

}
