package com.github.javaparser.ast.validator;

import com.github.javaparser.Problem;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.nodeTypes.NodeWithTokenRange;

import java.util.function.Consumer;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * A simple interface where validators can report found problems.
 */
public class ProblemReporter {
    private final Consumer<Problem> problemConsumer;

    public ProblemReporter(Consumer<Problem> problemConsumer) {
        this.problemConsumer = problemConsumer;
    }

    /**
     * Report a problem.
     *
     * @param message description of the problem
     * @param node the node in which the problem occurred, used to find the Range of the problem.
     */
    public void report(NodeWithTokenRange<?> node, String message, Object... args) {
        report(node.getTokenRange().orElse(null), message, args);
    }

    public void report(TokenRange range, String message, Object... args) {
        problemConsumer.accept(new Problem(f(message, args), range, null));
    }
}
