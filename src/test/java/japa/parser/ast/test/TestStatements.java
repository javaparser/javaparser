package japa.parser.ast.test;

import japa.parser.JavaParser;
import japa.parser.ast.stmt.BlockStmt;
import japa.parser.ast.stmt.Statement;
import junit.framework.Assert;

import org.junit.Test;

public class TestStatements {

	@Test
	public void testBlockStatement() throws Exception {
		BlockStmt bs = JavaParser.parseBlock("{return x+y;}");

		Assert.assertNotNull(bs);
	}

	@Test
	public void testStatement() throws Exception {
		Statement stmt = JavaParser.parseStatement("x = x+y;");
		Assert.assertNotNull(stmt);
	}
}
