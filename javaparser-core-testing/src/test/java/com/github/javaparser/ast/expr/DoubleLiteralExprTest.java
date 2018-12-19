package com.github.javaparser.ast.expr;

import org.junit.Assert;
import org.junit.Test;

import static com.github.javaparser.JavaParser.parseExpression;

public class DoubleLiteralExprTest {
    @Test
    public void test1() {
        float x = 0x0.00_00_02p-126f;
        DoubleLiteralExpr e = parseExpression("0x0.00_00_02p-126f");
        Assert.assertEquals(x, e.asDouble(), 0.0);
    }

    @Test
    public void test2() {
        double x = 0x0.000_000_000_000_1p-1_022;
        DoubleLiteralExpr e = parseExpression("0x0.000_000_000_000_1p-1_022");
        Assert.assertEquals(x, e.asDouble(), 0.0);
    }

    @Test
    public void test3() {
        double a = 0x1.p+1;
        DoubleLiteralExpr e = parseExpression("0x1.p+1");
        Assert.assertEquals(a, e.asDouble(), 0.0);
    }

    @Test
    public void test4() {
        double a = 0x.0p0;
        DoubleLiteralExpr e = parseExpression("0x.0p0");
        Assert.assertEquals(a, e.asDouble(), 0.0);
    }

    @Test
    public void test5() {
        double x = 0x0_0.0_0p-1_0;
        DoubleLiteralExpr e = parseExpression("0x0_0.0_0p-1_0");
        Assert.assertEquals(x, e.asDouble(), 0.0);
    }
}
