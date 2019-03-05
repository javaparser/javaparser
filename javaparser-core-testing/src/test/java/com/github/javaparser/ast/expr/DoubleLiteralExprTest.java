package com.github.javaparser.ast.expr;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseExpression;

class DoubleLiteralExprTest {
    @Test
    void test1() {
        float x = 0x0.00_00_02p-126f;
        DoubleLiteralExpr e = parseExpression("0x0.00_00_02p-126f");
        Assertions.assertEquals(x, e.asDouble());
    }

    @Test
    void test2() {
        double x = 0x0.000_000_000_000_1p-1_022;
        DoubleLiteralExpr e = parseExpression("0x0.000_000_000_000_1p-1_022");
        Assertions.assertEquals(x, e.asDouble());
    }

    @Test
    void test3() {
        double a = 0x1.p+1;
        DoubleLiteralExpr e = parseExpression("0x1.p+1");
        Assertions.assertEquals(a, e.asDouble());
    }

    @Test
    void test4() {
        double a = 0x.0p0;
        DoubleLiteralExpr e = parseExpression("0x.0p0");
        Assertions.assertEquals(a, e.asDouble());
    }

    @Test
    void test5() {
        double x = 0x0_0.0_0p-1_0;
        DoubleLiteralExpr e = parseExpression("0x0_0.0_0p-1_0");
        Assertions.assertEquals(x, e.asDouble());
    }
}
