package com.github.javaparser.ast.key;

import com.github.javaparser.*;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.07.26)
 */
public class FPLiteralTest {
    @Test
    void testLiteral() {
        var expr = StaticJavaParser.parseExpression("2./a");
        System.out.println(expr);

        Assertions.assertThrows(ParseProblemException.class,
                () -> StaticJavaParser.parseExpression("2..a"));
    }
}
