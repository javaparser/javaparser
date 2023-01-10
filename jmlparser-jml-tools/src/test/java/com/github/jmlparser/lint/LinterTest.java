package com.github.jmlparser.lint;

import com.github.jmlparser.TestWithJavaParser;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

import java.util.Collections;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
class LinterTest extends TestWithJavaParser {
    @Test
    void everythingWrong() {
        var result = parser.parse(getClass().getResourceAsStream("EverythingWrong.java"));
        Assumptions.assumeTrue(result.isSuccessful());
        var actual =
                new JmlLintingFacade(new JmlLintingConfig()).lint(Collections.singletonList(result.getResult().get()));

        for (LintProblem lintProblem : actual) {
            System.out.println(lintProblem);
        }
    }
}
