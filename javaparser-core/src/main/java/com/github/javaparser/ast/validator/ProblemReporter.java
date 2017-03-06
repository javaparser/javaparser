package com.github.javaparser.ast.validator;

import com.github.javaparser.Problem;
import com.github.javaparser.Range;
import com.github.javaparser.ast.nodeTypes.NodeWithRange;

import java.util.List;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

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
    public void report(NodeWithRange<?> node, String message, Object... args) {
        report(node.getRange().orElse(null), message, args);
    }

    public void report(Range range, String message, Object... args) {
        problems.add(new Problem(f(message, args), range, null));
    }
}
