package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.stmt.BlockStmt;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import java.io.File;
import java.io.IOException;

/**
 * @author Didier Villevalois
 */
@RunWith(JUnit4.class)
public class LexTest {

    @Test
    public void simpleLex() throws ParseException {
        String content = "(1   == 2)  = 9";
        Node node = JavaParser.parseExpression(content);
        Assert.assertEquals(content, node.toString());
    }

    @Test
    public void simpleComments() throws ParseException {
        String content = "1 /* Bingo */ + 2 // Bim\n * 3 // Oh yeah";
        Node node = JavaParser.parseExpression(content);
        Assert.assertEquals(content, node.toString());
    }

    @Test
    public void complexComments() throws ParseException {
        BlockStmt node = JavaParser.parseBlock("{\n" +
                "\t// Leading comment of doStuff1()\n" +
                "\tdoStuff1();\n" +
                "\t// Dangling comment of block\n" +
                "\n" +
                "\t// Leading comment 1 of doStuff2()\n" +
                "\t// Leading comment 2 of doStuff2()\n" +
                "\tdoStuff2();\n" +
                "}");

        Assert.assertEquals("// Dangling comment of block",
                node.getCommentAttributes().getDanglingComments().get(0).image());
        Assert.assertEquals("// Leading comment of doStuff1()",
                node.getStmts().get(0).getCommentAttributes().getLeadingComments().get(0).image());
        Assert.assertEquals("// Leading comment 1 of doStuff2()",
                node.getStmts().get(1).getCommentAttributes().getLeadingComments().get(0).image());
        Assert.assertEquals("// Leading comment 2 of doStuff2()",
                node.getStmts().get(1).getCommentAttributes().getLeadingComments().get(1).image());
    }

    @Test
    public void parseRandoopTest0() throws IOException, ParseException {
        CompilationUnit cu = JavaParser.parse(
                new File(getClass().getResource("bdd/samples/RandoopTest0.java").getPath()),
                null, true, false);
        Assert.assertNotNull(cu.toString());
    }
}
