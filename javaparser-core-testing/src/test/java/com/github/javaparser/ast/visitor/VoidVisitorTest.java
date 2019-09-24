package com.github.javaparser.ast.visitor;

import java.io.IOException;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.expr.ObjectCreationExpr;

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
