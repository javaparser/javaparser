/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser.ast.expr;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verifyNoInteractions;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.observer.AstObserver;
import java.math.BigInteger;
import org.assertj.core.data.Percentage;
import org.junit.jupiter.api.Test;

@SuppressWarnings("OctalInteger")
class LiteralStringValueExprTest {

    private final JavaParserAdapter parser = StaticJavaParser.newParserAdapter();

    @Test
    void trivialLiteralsAreConverted() {
        assertThat(new CharLiteralExpr('\t').getValue()).isEqualTo("\\t");
        assertThat(new CharLiteralExpr('\b').getValue()).isEqualTo("\\b");
        assertThat(new CharLiteralExpr('\f').getValue()).isEqualTo("\\f");
        assertThat(new CharLiteralExpr('\r').getValue()).isEqualTo("\\r");
        assertThat(new CharLiteralExpr('\n').getValue()).isEqualTo("\\n");
        assertThat(new CharLiteralExpr('\\').getValue()).isEqualTo("\\\\");
        assertThat(new CharLiteralExpr('\"').getValue()).isEqualTo("\\\"");

        assertThat(new IntegerLiteralExpr("0B0").asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr("0b0").asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr("0X0").asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr("0x0").asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr(0).asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr(00).asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr(0B0).asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr(0b0).asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr(0X0).asInt()).isEqualTo(0);
        assertThat(new IntegerLiteralExpr(0x0).asInt()).isEqualTo(0);

        assertThat(new LongLiteralExpr("0B0L").asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr("0b0L").asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr("0X0L").asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr("0x0L").asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr(0L).asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr(00L).asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr(0B0L).asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr(0b0L).asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr(0X0L).asLong()).isEqualTo(0);
        assertThat(new LongLiteralExpr(0x0L).asLong()).isEqualTo(0);

        assertThat(new DoubleLiteralExpr("0.0f").asDouble()).isEqualTo(0.0);
        assertThat(new DoubleLiteralExpr("0.0F").asDouble()).isEqualTo(0.0);
        assertThat(new DoubleLiteralExpr("0.0d").asDouble()).isEqualTo(0.0);
        assertThat(new DoubleLiteralExpr("0.0D").asDouble()).isEqualTo(0.0);
        assertThat(new DoubleLiteralExpr(0.0F).asDouble()).isEqualTo(0.0);
        assertThat(new DoubleLiteralExpr(0.0f).asDouble()).isEqualTo(0.0);
        assertThat(new DoubleLiteralExpr(0.0D).asDouble()).isEqualTo(0.0);
        assertThat(new DoubleLiteralExpr(0.0d).asDouble()).isEqualTo(0.0);
    }

    @Test
    void lowerAndUpperBoundIntegersAreConverted() {
        IntegerLiteralExpr dec = parser.parseExpression("2147483647");
        IntegerLiteralExpr posOct = parser.parseExpression("0177_7777_7777");
        IntegerLiteralExpr negOct = parser.parseExpression("0377_7777_7777");
        IntegerLiteralExpr posHex = parser.parseExpression("0x7fff_ffff");
        IntegerLiteralExpr negHex = parser.parseExpression("0xffff_ffff");
        IntegerLiteralExpr posBin = parser.parseExpression("0b0111_1111_1111_1111_1111_1111_1111_1111");
        IntegerLiteralExpr negBin = parser.parseExpression("0b1000_0000_0000_0000_0000_0000_0000_0000");

        assertThat(dec.asInt()).isEqualTo(2147483647);
        assertThat(posOct.asInt()).isEqualTo(2147483647); // 0177_7777_7777
        assertThat(negOct.asInt()).isEqualTo(-1); // 0377_7777_7777
        assertThat(posHex.asInt()).isEqualTo(0x7fff_ffff);
        assertThat(negHex.asInt()).isEqualTo(0xffff_ffff);
        assertThat(posBin.asInt()).isEqualTo(0b0111_1111_1111_1111_1111_1111_1111_1111);
        assertThat(negBin.asInt()).isEqualTo(0b1000_0000_0000_0000_0000_0000_0000_0000);
    }

    @Test
    void negativeLiteralValues() {
        UnaryExpr unaryIntExpr = parser.parseExpression("-2147483648"); // valid, Integer.MIN_VALUE
        IntegerLiteralExpr literalIntExpr = (IntegerLiteralExpr) unaryIntExpr.getExpression();
        IntegerLiteralExpr notValidIntExpr = parser.parseExpression("2147483648"); // not valid

        UnaryExpr unaryLongExpr = parser.parseExpression("-9223372036854775808L"); // valid, Long.MIN_VALUE
        LongLiteralExpr literalLongExpr = (LongLiteralExpr) unaryLongExpr.getExpression();
        LongLiteralExpr notValidLongExpr = parser.parseExpression("9223372036854775808L"); // not valid

        assertThat(literalIntExpr.asNumber()).isEqualTo(2147483648L);
        assertThat(literalLongExpr.asNumber()).isEqualTo(new BigInteger("9223372036854775808"));

        assertThatThrownBy(notValidIntExpr::asNumber).isInstanceOf(NumberFormatException.class);
        assertThatThrownBy(notValidLongExpr::asNumber).isInstanceOf(NumberFormatException.class);
    }

    @Test
    void lowerAndUpperBoundLongsAreConverted() {
        LongLiteralExpr dec = parser.parseExpression("9223372036854775807L");
        LongLiteralExpr posOct = parser.parseExpression("07_7777_7777_7777_7777_7777L");
        LongLiteralExpr negOct = parser.parseExpression("010_0000_0000_0000_0000_0000L");
        LongLiteralExpr posHex = parser.parseExpression("0x7fff_ffff_ffff_ffffL");
        LongLiteralExpr negHex = parser.parseExpression("0xffff_ffff_ffff_ffffL");
        LongLiteralExpr posBin =
                parser.parseExpression("0b0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111L");
        LongLiteralExpr negBin =
                parser.parseExpression("0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000L");

        assertThat(dec.asLong()).isEqualTo(9223372036854775807L);
        assertThat(posOct.asLong()).isEqualTo(9223372036854775807L); // 07_7777_7777_7777_7777_7777L
        assertThat(negOct.asLong()).isEqualTo(-9223372036854775808L); // 010_0000_0000_0000_0000_0000L
        assertThat(posHex.asLong()).isEqualTo(0x7fff_ffff_ffff_ffffL);
        assertThat(negHex.asLong()).isEqualTo(0xffff_ffff_ffff_ffffL);
        assertThat(posBin.asLong())
                .isEqualTo(0b0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111L);
        assertThat(negBin.asLong())
                .isEqualTo(0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000L);
    }

    @Test
    void charLiteralsAreConverted() {
        CharLiteralExpr a = parser.parseExpression("'a'");
        CharLiteralExpr percent = parser.parseExpression("'%'");
        CharLiteralExpr tab = parser.parseExpression("'\\t'");
        CharLiteralExpr newLine = parser.parseExpression("'\\n'");
        CharLiteralExpr slash = parser.parseExpression("'\\\\'");
        CharLiteralExpr quote = parser.parseExpression("'\\''");
        CharLiteralExpr omega = parser.parseExpression("'\\u03a9'");
        CharLiteralExpr unicode = parser.parseExpression("'\\uFFFF'");
        CharLiteralExpr ascii = parser.parseExpression("'\\177'");
        CharLiteralExpr trademark = parser.parseExpression("'™'");

        assertThat(a.asChar()).isEqualTo('a');
        assertThat(percent.asChar()).isEqualTo('%');
        assertThat(tab.asChar()).isEqualTo('\t');
        assertThat(newLine.asChar()).isEqualTo('\n');
        assertThat(slash.asChar()).isEqualTo('\\');
        assertThat(quote.asChar()).isEqualTo('\'');
        assertThat(omega.asChar()).isEqualTo('\u03a9');
        assertThat(unicode.asChar()).isEqualTo('\uFFFF');
        assertThat(ascii.asChar()).isEqualTo('\177');
        assertThat(trademark.asChar()).isEqualTo('™');
    }

    @Test
    void lowerAndUpperBoundDoublesAreConverted() {
        DoubleLiteralExpr posFloat = parser.parseExpression("3.4028235e38f");
        DoubleLiteralExpr negFloat = parser.parseExpression("1.40e-45f");
        DoubleLiteralExpr posDouble = parser.parseExpression("1.7976931348623157e308");
        DoubleLiteralExpr negDouble = parser.parseExpression("4.9e-324");
        DoubleLiteralExpr posHexFloat = parser.parseExpression("0x1.fffffffffffffp1023");
        DoubleLiteralExpr negHexFloat = parser.parseExpression("0x0.0000000000001P-1022");

        assertThat(posFloat.asDouble()).isCloseTo(3.4028235e38f, Percentage.withPercentage(1));
        assertThat(negFloat.asDouble()).isCloseTo(1.40e-45f, Percentage.withPercentage(1));
        assertThat(posDouble.asDouble()).isEqualTo(1.7976931348623157e308);
        assertThat(negDouble.asDouble()).isEqualTo(4.9e-324);
        assertThat(posHexFloat.asDouble()).isEqualTo(0x1.fffffffffffffp1023);
        assertThat(negHexFloat.asDouble()).isEqualTo(0x0.0000000000001P-1022);
    }

    @Test
    void specialCharactersInStringsAreEscaped() {
        assertThat(new StringLiteralExpr("\n").getValue()).isEqualTo("\\n");
        assertThat(new StringLiteralExpr("\r").getValue()).isEqualTo("\\r");
        assertThat(new StringLiteralExpr("").setEscapedValue("\n").getValue()).isEqualTo("\\n");
        assertThat(new StringLiteralExpr("").setEscapedValue("\r").getValue()).isEqualTo("\\r");
        assertThat(new StringLiteralExpr("").setEscapedValue("\n").asString()).isEqualTo("\n");
        assertThat(new StringLiteralExpr("").setEscapedValue("\r").asString()).isEqualTo("\r");
        assertThat(new StringLiteralExpr("Hello\nWorld\rHello\"World\'").asString())
                .isEqualTo("Hello\nWorld\rHello\"World\'");
    }

    @Test
    void issue4791Test() {
        String a = new String("Hello World");
        String b = new String("Hello World");
        StringLiteralExpr expression = new StringLiteralExpr(a);

        AstObserver observer = mock(AstObserver.class);
        expression.register(observer);

        expression.setValue(b);

        verifyNoInteractions(observer);
    }
}
