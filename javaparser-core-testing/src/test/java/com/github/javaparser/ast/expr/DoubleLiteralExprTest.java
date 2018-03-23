package com.github.javaparser.ast.expr;

import org.junit.Test;

import static com.github.javaparser.JavaParser.parseExpression;

public class DoubleLiteralExprTest {
    @Test
    public void test1() {
        float x = 0x0.00_00_02p-126f;
        parseExpression("0x0.00_00_02p-126f");
    }

    @Test
    public void test2() {
        double x = 0x0.000_000_000_000_1p-1_022;
        parseExpression("0x0.000_000_000_000_1p-1_022");
    }

    @Test
    public void test3() {
        double a = 0x1.p+1;
        parseExpression("0x1.p+1");
    }

    @Test
    public void test4() {
        double a = 0x.0p0;
        parseExpression("0x.0p0");
    }

    @Test
    public void test5() {
        double x = 0x0_0.0_0p-1_0;
        parseExpression("0x0_0.0_0p-1_0");
    }
}
