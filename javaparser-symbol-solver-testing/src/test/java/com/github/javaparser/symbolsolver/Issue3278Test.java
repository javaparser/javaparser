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

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledForJreRange;
import org.junit.jupiter.api.condition.JRE;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;

public class Issue3278Test extends AbstractResolutionTest {

    @Test
    void test() {
    		String code = 
        		"public class Foo {\n"
        		+ "	    public static void main(String[] args) {\n"
        		+ "	        A a = null;\n"
        		+ "	        m((a == null ? \"null\" : a.getB()));\n"
        		+ "	    }\n"
        		+ "	    void m(Comparable<? extends Comparable> obj) {}\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	class A{\n"
        		+ "	    private B b;\n"
        		+ "	    public A(B b){\n"
        		+ "	        this.b = b;\n"
        		+ "	    }\n"
        		+ "	    public B getB(){\n"
        		+ "	        return b;\n"
        		+ "	    }\n"
        		+ "	}\n"
        		+ "\n"
        		+ "	class B implements Comparable<B>{\n"
        		+ "\n"
        		+ "		@Override\n"
        		+ "		public int compareTo(B o) {\n"
        		+ "			return 0;\n"
        		+ "		}\n"
        		+ "	}";

    	JavaParserAdapter parser = JavaParserAdapter.of(createParserWithResolver(defaultTypeSolver()));

    	CompilationUnit cu = parser.parse(code);
    	
		ConditionalExpr expr = cu.findFirst(ConditionalExpr.class).get();

		assertEquals("java.lang.Comparable<? extends java.lang.Comparable>", expr.calculateResolvedType().describe());
    }
}
