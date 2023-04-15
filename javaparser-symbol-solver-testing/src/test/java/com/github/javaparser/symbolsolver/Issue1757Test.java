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
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class Issue1757Test extends AbstractResolutionTest {

    @Test()
    void test() throws IOException {
        
        String src =
                "import java.util.Comparator;\n" + 
                "public class A {\n" + 
                "    public void m() {\n" + 
                "        Comparator<String> c = new Comparator<String>() {\n" + 
                "            public int compare(String o1, String o2) {\n" + 
                "                return 0;\n" + 
                "            }\n" + 
                "        };\n" + 
                "    }\n" + 
                "}";

        ParserConfiguration config = new ParserConfiguration();
        config.setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver()));
        StaticJavaParser.setConfiguration(config);

        CompilationUnit cu = StaticJavaParser.parse(src);
        
        ObjectCreationExpr oce = cu.findFirst(ObjectCreationExpr.class).get();
        assertEquals("java.util.Comparator<java.lang.String>", oce.calculateResolvedType().describe());
        assertTrue(oce.resolve().getQualifiedName().startsWith("A.Anonymous"));
    }
    
}
