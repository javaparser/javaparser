package com.github.javaparser.ast.stmt;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
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
}
