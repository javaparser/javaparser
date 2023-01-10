package com.github.jmlparser.wd;

import com.github.javaparser.JavaParser;
import com.github.jmlparser.SolverTest;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;

import static com.github.jmlparser.wd.WellDefinednessMain.isWelldefined;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Alexander Weigl
 * @version 1 (14.06.22)
 */
class WDVisitorExprTest {
    private final JavaParser parser = new JavaParser();

    @ParameterizedTest
    @CsvFileSource(resources = "wd-expr.csv", delimiterString = "§")
    void wdExpression(String expr) {
        Assumptions.assumeTrue(SolverTest.z3Installed());
        assertTrue(isWelldefined(parser, expr));
    }

    @ParameterizedTest
    @CsvFileSource(resources = "not-wd-expr.csv", delimiterString = "§")
    void wdExpressionError(String expr) {
        Assumptions.assumeTrue(SolverTest.z3Installed());
        assertFalse(isWelldefined(parser, expr));
    }
}
