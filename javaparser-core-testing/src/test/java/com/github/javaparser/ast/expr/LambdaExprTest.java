package com.github.javaparser.ast.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Node;
import org.junit.Test;

import static com.github.javaparser.JavaParser.getInternalParser;
import static org.junit.Assert.*;

public class LambdaExprTest {
    @Test
    public void lambdaRange1(){
        Expression expression = getInternalParser().parseExpression("x -> y");
        assertRange("x", "y", expression);
    }

    @Test
    public void lambdaRange2(){
        Expression expression = getInternalParser().parseExpression("(x) -> y");
        assertRange("(", "y", expression);
    }

    private void assertRange(String startToken, String endToken, Node node) {
        TokenRange tokenRange = node.getTokenRange().get();
        assertEquals(startToken, tokenRange.getBegin().asString());
        assertEquals(endToken, tokenRange.getEnd().asString());
    }

    @Test
    public void getExpressionBody(){
        LambdaExpr lambdaExpr = getInternalParser().parseExpression("x -> y").asLambdaExpr();
        assertEquals("Optional[y]", lambdaExpr.getExpressionBody().toString());
    }

    @Test
    public void getNoExpressionBody(){
        LambdaExpr lambdaExpr = getInternalParser().parseExpression("x -> {y;}").asLambdaExpr();
        assertEquals("Optional.empty", lambdaExpr.getExpressionBody().toString());
    }

}