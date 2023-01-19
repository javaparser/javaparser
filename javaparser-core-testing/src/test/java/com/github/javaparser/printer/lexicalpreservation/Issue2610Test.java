/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import org.junit.jupiter.api.Test;

import java.util.Optional;

public class Issue2610Test extends AbstractLexicalPreservingTest {
    
    /*
     * This test case must prevent an UnsupportedOperation Removed throwed by LexicalPreservation when we try to replace an expression
     */
    @Test
    public void test() {
      
        considerCode(
                "public class Bar {\n" + 
                "    public void foo() {\n" + 
                "          // comment\n" +
                "          System.out.print(\"error\");\n" +
                "    }\n" +
                "}"
                );
        // contruct a statement with a comment
        Expression expr = StaticJavaParser.parseExpression("System.out.println(\"warning\")");
        // Replace the method expression
        Optional<MethodCallExpr> mce = cu.findFirst(MethodCallExpr.class);
        mce.get().getParentNode().get().replace(mce.get(), expr);
        // TODO assert something
    }
}
