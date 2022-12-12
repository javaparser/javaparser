package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;

public class Issue3441Test extends AbstractLexicalPreservingTest {

	@Test
	void test() {
		    considerCode( 
		    		"public class Foo {\n" +
		    	     "    void bar() {\n" +
		    	     "        stmt1(); // comment 1\n" +
		    	     "        stmt2(); // comment 2\n" +
		    	     "    }\n" +
		    	     "}");
		    String expected = 
		    		"public class Foo {\n" +
		   	    	"    void bar() {\n" +
		   	    	"        stmt2(); // comment 2\n" +
		   	    	"    }\n" +
		   	    	"}";
		    
		BlockStmt block = cu.findFirst(BlockStmt.class).get();
	    Statement stmt = block.getStatements().get(0);
	    
	    block.remove(stmt);
	    
	    assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
	}
    
}
