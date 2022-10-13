package com.github.jmlparser.lint;

import com.github.javaparser.Problem;
import com.github.javaparser.TokenRange;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
public class LintProblem extends Problem {
    public LintProblem(String message, TokenRange location, Throwable cause, Severity level) {
        super(message, location, cause);
    }
}
