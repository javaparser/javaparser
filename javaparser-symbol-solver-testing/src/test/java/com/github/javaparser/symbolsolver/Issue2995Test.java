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

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class Issue2995Test extends AbstractResolutionTest {

    @Test
    public void test() {
        ParserConfiguration config = new ParserConfiguration().setSymbolResolver(new JavaSymbolSolver(new ReflectionTypeSolver(false)));
        StaticJavaParser.setConfiguration(config);

        String str = "public class MyClass {\n" +
                "   class Inner1 {\n" +
                "       class Inner2 {\n" +
                "       }\n" +
                "   }\n" +
                "   {\n" +
                "       new Inner1().new Inner2();\n" +
                "   }\n" +
                "}\n";
        CompilationUnit cu = StaticJavaParser.parse(str);
        List<ObjectCreationExpr> exprs = cu.findAll(ObjectCreationExpr.class);
        assertEquals("new Inner1().new Inner2()", exprs.get(0).toString());
        assertEquals("MyClass.Inner1.Inner2", exprs.get(0).getType().resolve().describe());
        assertEquals("new Inner1()", exprs.get(1).toString());
        assertEquals("MyClass.Inner1", exprs.get(1).getType().resolve().describe());
    }
}
