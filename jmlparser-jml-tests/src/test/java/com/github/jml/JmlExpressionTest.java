package com.github.jml;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.expr.Expression;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;

/**
 * @author Alexander Weigl
 * @version 1 (11.07.22)
 */
class JmlExpressionTest {
    private JavaParser javaParser = new JavaParser();

    @ParameterizedTest
    @CsvFileSource(resources = "/jml-exprs.txt", delimiterString = "FOOBARBAZ")
    void parse(String input) {
        ParseResult<Expression> r = javaParser.parseJmlExpression(input);
        if (!r.isSuccessful()) {
            r.getProblems().forEach(System.out::println);
        }
        Assertions.assertTrue(r.isSuccessful());
    }
}
