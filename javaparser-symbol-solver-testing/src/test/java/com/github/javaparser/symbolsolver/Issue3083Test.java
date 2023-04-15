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
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

public class Issue3083Test extends AbstractResolutionTest {

    @Test
    void test() {
        String code = 
                "class A {\n" + 
                "        public void getFromMap() {\n" + 
                "            final java.util.Map<String, String> expected = new java.util.HashMap<>();\n" + 
                "            java.util.Map.Entry<String, String> entry = get(expected, 0);\n" + 
                "        }\n" + 
                "        <V, K> java.util.Map.Entry<K,V> get(java.util.Map<K,V> map, int index) {\n" + 
                "            return null;\n" + 
                "        }\n" + 
                "        Object get(Object map, int index) {\n" + 
                "            return null;\n" + 
                "        }\n" + 
                "    }";
        ParserConfiguration config = new ParserConfiguration();
        StaticJavaParser.getConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        CompilationUnit cu = StaticJavaParser.parse(code);
        MethodCallExpr mce = cu.findFirst(MethodCallExpr.class).get();
        // this test must not throw a MethodAmbiguityException on the get(expected, 0) call
        mce.resolve();
    }

}
