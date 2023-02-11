package com.github.jmlparser.lint;

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

    public void warn(NodeWithTokenRange<?> node, String category, String ruleId, String message, Object... args) {
        report(LintRule.WARN, node.getTokenRange().orElse(null), category, ruleId, message, args);
    }

    public void hint(NodeWithTokenRange<?> node, String category, String ruleId, String message, Object... args) {
        report(LintRule.HINT, node.getTokenRange().orElse(null), category, ruleId, message, args);
    }

    public void error(NodeWithTokenRange<?> node, String category, String ruleId, String message, Object... args) {
        report(LintRule.ERROR, node.getTokenRange().orElse(null), category, ruleId, message, args);
    }

    public void report(String level, TokenRange range, String category, String ruleId, String message, Object... args) {
        problemConsumer.accept(new LintProblem(level, f(message, args), range, null, category, ruleId));
    }

    public void report(LintProblem lintProblem) {
        problemConsumer.accept(lintProblem);
    }
}

