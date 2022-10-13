package com.github.jmlparser.lint;

import com.github.javaparser.ast.Node;
import com.github.javaparser.utils.Log;
import org.jetbrains.annotations.NotNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlLintingFacade {
    private static final Logger LOGGER = LoggerFactory.getLogger(JmlLintingFacade.class);

    private JmlLintingFacade() {

    }

    public static List<LintRule> getLinter(JmlLintingConfig config) {
        ServiceLoader<LintRule> loader = ServiceLoader.load(LintRule.class);
        List<LintRule> validators = new ArrayList<>(64);
        for (LintRule lintRule : loader) {
            if (!config.isDisabled(lintRule)) {
                validators.add(lintRule);
            }
        }
        return validators;
    }

    public static void lint(@NotNull JmlLintingConfig config, LintProblemReporter reporter, Collection<? extends Node> nodes) {
        var linters = getLinter(config);
        for (Node it : nodes) {
            for (LintRule linter : linters) {
                try {
                    linter.accept(it, reporter);
                } catch (Exception e) {
                    LOGGER.error("Error in linter: {}", linter.getClass().getName(), e);
                }
            }
        }
    }

    public static Collection<LintProblem> lint(@NotNull JmlLintingConfig config, @NotNull Collection<? extends Node> nodes) {
        var problems = new ArrayList<LintProblem>(1024);
        Consumer<LintProblem> collector = problems::add;
        lint(config, new LintProblemReporter(collector), nodes);
        problems.sort(Comparator.comparing(it -> it.getLocation().get().toRange().get().begin));
        return problems;
    }

}
