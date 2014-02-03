package japa.parser.ast.test;

import static org.junit.Assert.assertNotNull;
import japa.parser.JavaParser;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.Statement;

import org.junit.Test;

public class TestStatements {

	@Test
	public void testBlockStatement() throws Exception {
		BlockStmt bs = JavaParser.parseBlock("{return x+y;}");

		assertNotNull(bs);
	}

	@Test
	public void testStatement() throws Exception {
		Statement stmt = JavaParser.parseStatement("x = x+y;");
		assertNotNull(stmt);
	}
}
