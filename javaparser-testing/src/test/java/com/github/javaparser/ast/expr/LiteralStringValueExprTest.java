package com.github.javaparser.ast.expr;

import org.junit.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * @author Artur Bosch
 */
public class LiteralStringValueExprTest {

    @Test
    public void longLiteralsAreConverted() {
        LongLiteralExpr literalExpr = new LongLiteralExpr(25L);

        assertThat(literalExpr.asLong()).isEqualTo(25L);
    }

    @Test
    public void integerLiteralsAreConverted() {
        IntegerLiteralExpr literalExpr = new IntegerLiteralExpr(25);

        assertThat(literalExpr.asInt()).isEqualTo(25);
    }

    @Test
    public void charLiteralsAreConverted() {
        CharLiteralExpr literalExpr = new CharLiteralExpr('\t');

        assertThat(literalExpr.asChar()).isEqualTo('\t');
    }

    @Test
    public void doubleLiteralsAreConverted() {
        DoubleLiteralExpr literalExpr = new DoubleLiteralExpr(25.0d);

        assertThat(literalExpr.asDouble()).isEqualTo(25.0d);
    }

}
