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
