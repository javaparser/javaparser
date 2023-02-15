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

package com.github.javaparser.ast.visitor;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

public class VoidVisitorTest {
	@Test()
    void compareFindAllSizeWithVoidVisitorAdapterSize() throws IOException {
        CompilationUnit unit = createUnit();
        
        List<ObjectCreationExpr> oce = unit.findAll(ObjectCreationExpr.class);
        
        AtomicInteger foundObjs = new AtomicInteger(0);
		unit.accept(new VoidVisitorAdapter<Object>() {
            @Override
            public void visit(ObjectCreationExpr exp, Object arg) {
            	super.visit(exp, arg);
                ((AtomicInteger)arg).incrementAndGet();
            }            
        }, foundObjs);
        
		Assertions.assertEquals(oce.size(), foundObjs.get());
    }

	private CompilationUnit createUnit() {
		JavaParser javaParser = new JavaParser();

        CompilationUnit unit = javaParser.parse("public class Test\n" + 
        		"{\n" + 
        		"   public class InnerTest\n" + 
        		"   {\n" + 
        		"       public InnerTest() {}\n" + 
        		"   }\n" + 
        		"    \n" + 
        		"   public Test() {\n" + 
        		"   }\n" + 
        		"\n" + 
        		"   public static void main( String[] args ) { \n" + 
        		"       new Test().new InnerTest();\n" + 
        		"   }\n" + 
        		"}").getResult().get();
		return unit;
	}
    
    @Test()
    void testFindAllSize() throws IOException {
        CompilationUnit unit = createUnit();
        
        List<ObjectCreationExpr> oce = unit.findAll(ObjectCreationExpr.class);
        
        Assertions.assertEquals(2, oce.size());
    }
}
