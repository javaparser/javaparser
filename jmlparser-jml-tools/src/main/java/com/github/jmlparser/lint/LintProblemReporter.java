package com.github.jmlparser.lint;

import com.github.javaparser.Problem;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.nodeTypes.NodeWithTokenRange;

import java.util.function.Consumer;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
public class LintProblemReporter {
    private final Consumer<LintProblem> problemConsumer;

    public LintProblemReporter(Consumer<LintProblem> problemConsumer) {
        this.problemConsumer = problemConsumer;
    }

    public void warn(NodeWithTokenRange<?> node, String message, Object... args) {
        report(Severity.WARN, node.getTokenRange().orElse(null), message, args);
    }

    public void hint(NodeWithTokenRange<?> node, String message, Object... args) {
        report(Severity.HINT, node.getTokenRange().orElse(null), message, args);
    }

    public void error(NodeWithTokenRange<?> node, String message, Object... args) {
        report(Severity.ERROR, node.getTokenRange().orElse(null), message, args);
    }

    public void report(Severity level, TokenRange range, String message, Object... args) {
        problemConsumer.accept(new LintProblem(f(message, args), range, null, level));
    }
}

