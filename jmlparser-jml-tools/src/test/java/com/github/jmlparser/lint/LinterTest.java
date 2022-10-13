package com.github.jmlparser.lint;

import com.github.jmlparser.TestWithJavaParser;
import org.junit.Assume;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

import java.util.Collections;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
public class LinterTest extends TestWithJavaParser {
    @Test
    void everythingWrong() {
        var result = parser.parse(getClass().getResourceAsStream("EverythingWrong.java"));
        Assumptions.assumeTrue(result.isSuccessful());
        var actual =
                JmlLintingFacade.lint(new JmlLintingConfig(), Collections.singletonList(result.getResult().get()));

        for (LintProblem lintProblem : actual) {
            System.out.println(lintProblem);
        }
    }
}
