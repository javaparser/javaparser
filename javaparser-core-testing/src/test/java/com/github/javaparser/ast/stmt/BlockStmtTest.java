package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import org.junit.Test;

public class BlockStmtTest {
    @Test
    public void issue748AddingIdenticalStatementsDoesParentingRight() {
        BlockStmt blockStmt = new BlockStmt();
        Expression exp = new NameExpr("x");
        MethodCallExpr expression = new MethodCallExpr(exp, "y");

        blockStmt.addStatement(expression);
        blockStmt.addStatement(expression.clone());
        // This fails when the issue exists:
        String s = blockStmt.toString();
    }

}
