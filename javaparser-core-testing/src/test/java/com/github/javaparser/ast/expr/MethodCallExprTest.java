package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;
import static java.util.Optional.empty;
import static org.junit.jupiter.api.Assertions.assertEquals;

class MethodCallExprTest {
    
    @Test
    void replaceLambdaIssue1290() {
        MethodCallExpr methodCallExpr = parseExpression("callSomeFun(r -> r instanceof SomeType)").asMethodCallExpr();
        LambdaExpr lambdaExpr = methodCallExpr.getArgument(0).asLambdaExpr();
        MethodCallExpr lambdaWrapper = new MethodCallExpr("lambdaWrapper");
        lambdaExpr.replace(lambdaWrapper);
        
        assertEquals(2, methodCallExpr.getChildNodes().size());
        assertEquals(empty(), lambdaExpr.getParentNode());
    }

}