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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ast.expr.Expression.EXCLUDE_ENCLOSED_EXPR;
import static org.junit.jupiter.api.Assertions.assertEquals;

class NodeWithArgumentsTest extends AbstractLexicalPreservingTest {
    
    @Test
    void testGetArgumentPosition() {
        considerCode("" +
                "class Foo {\n" +
                "    Map<Integer,String> map = new HashMap<>();\n" +
                "    public String bar(int i) {\n" +
                "        return map.put(((i)),((\"baz\")));\n" +
                "    } \n" +
                "}");
        MethodCallExpr mce = cu.findFirst(MethodCallExpr.class).get();
        Expression arg0 = mce.getArgument(0);
        Expression arg1 = mce.getArgument(1);
        Expression innerExpr0 = arg0.asEnclosedExpr().getInner()
                .asEnclosedExpr().getInner();
        Expression innerExpr1 = arg1.asEnclosedExpr().getInner()
                .asEnclosedExpr().getInner();
        
        assertEquals(0, mce.getArgumentPosition(arg0)); // with no conversion
        assertEquals(0, mce.getArgumentPosition(innerExpr0, EXCLUDE_ENCLOSED_EXPR)); // with a conversion skipping EnclosedExprs
        assertEquals(1, mce.getArgumentPosition(arg1)); // with no conversion
        assertEquals(1, mce.getArgumentPosition(innerExpr1, EXCLUDE_ENCLOSED_EXPR)); // with a conversion skipping EnclosedExprs
    }
}
