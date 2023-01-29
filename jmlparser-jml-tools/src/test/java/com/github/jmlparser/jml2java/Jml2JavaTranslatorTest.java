package com.github.jmlparser.jml2java;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.google.common.truth.Truth;
import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (11.10.22)
 */
class Jml2JavaTranslatorTest {
    @Test
    void test() {
        JmlQuantifiedExpr n1 = StaticJavaParser.parseJmlExpression("(\\forall int x; 0 <= x < a.length; x%2==0)");
        var bound = Jml2JavaTranslator.findLowerBound(n1, "x");
        Truth.assertThat(bound.toString()).isEqualTo("0");
    }

    @Test
    void test2() {
        JmlQuantifiedExpr n1 = StaticJavaParser.parseJmlExpression("(\\forall int x; 5 < x < a.length; x%2==0)");
        var bound = Jml2JavaTranslator.findLowerBound(n1, "x");
        Truth.assertThat(bound.toString()).isEqualTo("5 + 1");
    }

    @Test
    void test3() {
        JmlQuantifiedExpr n1 = StaticJavaParser.parseJmlExpression("(\\forall int x; 2+1 < x < a.length; x%2==0)");
        var bound = Jml2JavaTranslator.findLowerBound(n1, "x");
        Truth.assertThat(bound.toString()).isEqualTo("2 + 1 + 1");
    }

    @Test
    void test6() {
        JmlQuantifiedExpr n1 = StaticJavaParser.parseJmlExpression("(\\forall int y; 2+1 < y < a.length; y%2==0)");
        var bound = Jml2JavaTranslator.findLowerBound(n1, "y");
        Truth.assertThat(bound.toString()).isEqualTo("2 + 1 + 1");
    }

    @Test
    void test4() {
        JmlQuantifiedExpr n1 = StaticJavaParser.parseJmlExpression("(\\forall int x; 0 < x && x < a.length; x%2==0)");
        var bound = Jml2JavaTranslator.findLowerBound(n1, "x");
        Truth.assertThat(bound.toString()).isEqualTo("0 + 1");
    }

    @Test
    void test5() {
        JmlQuantifiedExpr n1 = StaticJavaParser.parseJmlExpression("(\\forall int x; 0 <= x && x < a.length; x%2==0)");
        var bound = Jml2JavaTranslator.findLowerBound(n1, "x");
        Truth.assertThat(bound.toString()).isEqualTo("0");
    }
}