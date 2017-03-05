package com.github.javaparser.ast.validator;

import com.github.javaparser.Problem;
import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;

import java.util.List;

/**
 * A simple interface where validators can report found problems.
 */
public class ProblemReporter {
    private final List<Problem> problems;

    public ProblemReporter(List<Problem> problems) {
        this.problems = problems;
    }

    /**
     * Report a problem.
     *
     * @param message description of the problem
     * @param node the node in which the problem occurred, used to find the Range of the problem.
     */
    public void report(String message, Node node) {
        report(message, node.getRange().orElse(null));
    }

    public void report(String message, Range range) {
        problems.add(new Problem(message, range, null));
    }
}
