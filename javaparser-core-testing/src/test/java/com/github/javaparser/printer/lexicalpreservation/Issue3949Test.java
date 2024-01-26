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

package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;

class Issue3949Test extends AbstractLexicalPreservingTest  {

	@Test
    public void test() {
    	considerCode(
    			"class A {\n"
    					+ "\n"
    		            + "  void foo() {\n"
    		            + "    Consumer<Integer> lambda = a -> System.out.println(a);\n"
    		            + "  }\n"
    		            + "}");

    	ExpressionStmt estmt = cu.findAll(ExpressionStmt.class).get(1).clone();
    	LambdaExpr lexpr = cu.findAll(LambdaExpr.class).get(0);
        LexicalPreservingPrinter.setup(cu);

        BlockStmt block = new BlockStmt();
        BreakStmt bstmt = new BreakStmt();
        block.addStatement(new ExpressionStmt(estmt.getExpression()));
        block.addStatement(bstmt);
        lexpr.setBody(block);

        String expected =
        		"class A {\n"
        		+ "\n"
        		+ "  void foo() {\n"
        		+ "    Consumer<Integer> lambda = a -> {\n"
        		+ "        System.out.println(a);\n"
        		+ "        break;\n"
        		+ "    };\n"
        		+ "  }\n"
        		+ "}";

        assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }

}
