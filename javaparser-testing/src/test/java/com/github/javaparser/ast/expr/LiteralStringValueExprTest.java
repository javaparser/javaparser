/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2017 The JavaParser Team.
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

import com.github.javaparser.JavaParser;
import org.assertj.core.data.Percentage;
import org.junit.Test;

import static org.assertj.core.api.Assertions.assertThat;

public class LiteralStringValueExprTest {

    @Test
    public void longLiteralsAreConverted() {
        LongLiteralExpr dec = JavaParser.parseExpression("9223372036854775807L");
        LongLiteralExpr posOct = JavaParser.parseExpression("07_7777_7777_7777_7777_7777L");
        LongLiteralExpr negOct = JavaParser.parseExpression("010_0000_0000_0000_0000_0000L");
        LongLiteralExpr posHex = JavaParser.parseExpression("0x7fff_ffff_ffff_ffffL");
        LongLiteralExpr negHex = JavaParser.parseExpression("0xffff_ffff_ffff_ffffL");
        LongLiteralExpr posBin = JavaParser.parseExpression("0b0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111L");
        LongLiteralExpr negBin = JavaParser.parseExpression("0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000L");

        assertThat(dec.asLong()).isEqualTo(9223372036854775807L);
        assertThat(posOct.asLong()).isEqualTo(9223372036854775807L); // 07_7777_7777_7777_7777_7777L
        assertThat(negOct.asLong()).isEqualTo(-9223372036854775808L); // 010_0000_0000_0000_0000_0000L
        assertThat(posHex.asLong()).isEqualTo(0x7fff_ffff_ffff_ffffL);
        assertThat(negHex.asLong()).isEqualTo(0xffff_ffff_ffff_ffffL);
        assertThat(posBin.asLong()).isEqualTo(0b0111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111L);
        assertThat(negBin.asLong()).isEqualTo(0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000L);
    }

    @Test
    public void integerLiteralsAreConverted() {
        IntegerLiteralExpr dec = JavaParser.parseExpression("2147483647");
        IntegerLiteralExpr posOct = JavaParser.parseExpression("0177_7777_7777");
        IntegerLiteralExpr negOct = JavaParser.parseExpression("0377_7777_7777");
        IntegerLiteralExpr posHex = JavaParser.parseExpression("0x7fff_ffff");
        IntegerLiteralExpr negHex = JavaParser.parseExpression("0xffff_ffff");
        IntegerLiteralExpr posBin = JavaParser.parseExpression("0b0111_1111_1111_1111_1111_1111_1111_1111");
        IntegerLiteralExpr negBin = JavaParser.parseExpression("0b1000_0000_0000_0000_0000_0000_0000_0000");

        assertThat(dec.asInt()).isEqualTo(2147483647);
        assertThat(posOct.asInt()).isEqualTo(2147483647); // 0177_7777_7777
        assertThat(negOct.asInt()).isEqualTo(-1); // 0377_7777_7777
        assertThat(posHex.asInt()).isEqualTo(0x7fff_ffff);
        assertThat(negHex.asInt()).isEqualTo(0xffff_ffff);
        assertThat(posBin.asInt()).isEqualTo(0b0111_1111_1111_1111_1111_1111_1111_1111);
        assertThat(negBin.asInt()).isEqualTo(0b1000_0000_0000_0000_0000_0000_0000_0000);
    }

    @Test
    public void charLiteralsAreConverted() {
        Expression expr = JavaParser.parseExpression("'\\n'");

        assertThat(expr).isInstanceOf(CharLiteralExpr.class);
        assertThat(((CharLiteralExpr) expr).asChar()).isEqualTo('\\');
    }

    @Test
    public void doubleLiteralsAreConverted() {
        DoubleLiteralExpr posFloat = JavaParser.parseExpression("3.4028235e38f");
        DoubleLiteralExpr negFloat = JavaParser.parseExpression("1.40e-45f");
        DoubleLiteralExpr posDouble = JavaParser.parseExpression("1.7976931348623157e308");
        DoubleLiteralExpr negDouble = JavaParser.parseExpression("4.9e-324");

        assertThat(posFloat.asDouble()).isCloseTo(3.4028235e38f, Percentage.withPercentage(1));
        assertThat(negFloat.asDouble()).isCloseTo(1.40e-45f, Percentage.withPercentage(1));
        assertThat(posDouble.asDouble()).isEqualTo(1.7976931348623157e308);
        assertThat(negDouble.asDouble()).isEqualTo(4.9e-324);
    }

}
