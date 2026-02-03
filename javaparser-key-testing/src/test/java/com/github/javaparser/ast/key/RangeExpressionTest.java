package com.github.javaparser.ast.key;

import com.github.javaparser.*;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * Test for the conflicts between DOUBLE_LITERAL and RANGE_OPERATOR.
 * <p>
 * The input "5..6" is read as {@code <DOUBLE><DOUBLE>} as double literals are only to have a mandatory number
 * before or after decimal point.
 *
 * @author Alexander Weigl
 * @version 1 (01.01.25)
 */
public class RangeExpressionTest {
    @Test
    void test1() {
        var input = "5..6";
        var jp = new JavaParser();
        var stream = new StringProvider(input);
        var jj_input_stream = new SimpleCharStream(stream, 1, 1);
        var token_source = new GeneratedJavaParserTokenManager(jj_input_stream);
        token_source.setStoreTokens(true);
        var tok1 = token_source.getNextToken();
        var tok2 = token_source.getNextToken();
        var tok3 = token_source.getNextToken();
        var tok4 = token_source.getNextToken();

        Assertions.assertEquals("5", tok1.toString());
        Assertions.assertEquals(GeneratedJavaParserConstants.INTEGER_LITERAL, tok1.kind);
        Assertions.assertEquals("..", tok2.toString());
        Assertions.assertEquals(GeneratedJavaParserConstants.DOTDOT, tok2.kind);
        Assertions.assertEquals("6", tok3.toString());
        Assertions.assertEquals(GeneratedJavaParserConstants.INTEGER_LITERAL, tok3.kind);
        Assertions.assertEquals(GeneratedJavaParserConstants.EOF, tok4.kind);
    }
}
