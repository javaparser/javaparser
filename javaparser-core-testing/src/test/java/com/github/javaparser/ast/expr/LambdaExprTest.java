package com.github.javaparser.ast.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.type.UnknownType;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseBlock;
import static com.github.javaparser.StaticJavaParser.parseExpression;
import static com.github.javaparser.utils.TestUtils.assertEqualsNoEol;
import static org.junit.jupiter.api.Assertions.assertEquals;

class LambdaExprTest {
    @Test
    void lambdaRange1() {
        Expression expression = parseExpression("x -> y");
        assertRange("x", "y", expression);
    }

    @Test
    void lambdaRange2() {
        Expression expression = parseExpression("(x) -> y");
        assertRange("(", "y", expression);
    }

    private void assertRange(String startToken, String endToken, Node node) {
        TokenRange tokenRange = node.getTokenRange().get();
        assertEquals(startToken, tokenRange.getBegin().asString());
        assertEquals(endToken, tokenRange.getEnd().asString());
    }

    @Test
    void getExpressionBody() {
        LambdaExpr lambdaExpr = parseExpression("x -> y").asLambdaExpr();
        assertEquals("Optional[y]", lambdaExpr.getExpressionBody().toString());
    }

    @Test
    void getNoExpressionBody() {
        LambdaExpr lambdaExpr = parseExpression("x -> {y;}").asLambdaExpr();
        assertEquals("Optional.empty", lambdaExpr.getExpressionBody().toString());
    }

    @Test
    void oneParameterAndExpressionUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new Parameter(new UnknownType(), "a"), parseExpression("5"));
        assertEquals("a -> 5", expr.toString());
    }

    @Test
    void oneParameterAndStatementUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new Parameter(new UnknownType(), "a"), parseBlock("{return 5;}"));
        assertEqualsNoEol("a -> {\n    return 5;\n}", expr.toString());
    }

    @Test
    void multipleParametersAndExpressionUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new NodeList<>(new Parameter(new UnknownType(), "a"), new Parameter(new UnknownType(), "b")), parseExpression("5"));
        assertEquals("(a, b) -> 5", expr.toString());
    }

    @Test
    void multipleParametersAndStatementUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new NodeList<>(new Parameter(new UnknownType(), "a"), new Parameter(new UnknownType(), "b")), parseBlock("{return 5;}"));
        assertEqualsNoEol("(a, b) -> {\n    return 5;\n}", expr.toString());
    }

    @Test
    void zeroParametersAndStatementUtilityConstructor() {
        LambdaExpr expr = new LambdaExpr(new NodeList<>(), parseBlock("{return 5;}"));
        assertEqualsNoEol("() -> {\n    return 5;\n}", expr.toString());
    }

}