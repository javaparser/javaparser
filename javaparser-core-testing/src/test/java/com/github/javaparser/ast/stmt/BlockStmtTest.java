package com.github.javaparser.ast.stmt;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parse;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static com.github.javaparser.utils.Utils.EOL;

class BlockStmtTest {
    @Test
    void issue748AddingIdenticalStatementsDoesParentingRight() {
        BlockStmt blockStmt = new BlockStmt();
        Expression exp = new NameExpr("x");
        MethodCallExpr expression = new MethodCallExpr(exp, "y");

        blockStmt.addStatement(expression);
        blockStmt.addStatement(expression.clone());
        // This fails when the issue exists:
        String s = blockStmt.toString();
    }

    @Test
    void issue2099AddingAddingStatementAfterTraillingComment() {
        JavaParser javaParser = new JavaParser();

        Statement statement = javaParser.parseStatement(
            "if(value != null) {" + EOL +
            "    value.value();" + EOL +
            "}").getResult().get();

        BlockStmt blockStmt = LexicalPreservingPrinter.setup(
                javaParser.parseBlock("{" + EOL +
                "    value(); // Test" + EOL +
                "}").getResult().get());

        blockStmt.addStatement(statement);
        String s = LexicalPreservingPrinter.print(blockStmt);
        String expected = "{\n" +
                "    value(); // Test\n" +
                "    if(value != null) {\n" +
                "        value.value();\n" +
                "    }\n" +
                "}";
        System.out.println("EXPECTED:\n" + expected);
        System.out.println("RESULT:\n" + s);

        assertEqualsNoEol(expected, blockStmt.toString());
    }

}
