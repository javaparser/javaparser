package com.github.jmlparser.lint;

import com.github.javaparser.Problem;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.Validators;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.ServiceLoader;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlLintingFacade {
    public static Validators getLinter(JmlLintingConfig config) {
        ServiceLoader<LintRule> loader = ServiceLoader.load(LintRule.class);
        Validators validators = new Validators();
        for (LintRule lintRule : loader) {
            if (!config.isDisabled(lintRule)) {
                validators.add(lintRule);
            }
        }
        return validators;
    }

    public static void lint(@NotNull JmlLintingConfig config, ProblemReporter reporter, Collection<? extends Node> nodes) {
        Validators linter = getLinter(config);
        nodes.forEach(it -> linter.accept(it, reporter));
    }

    public static Collection<Problem> lint(@NotNull JmlLintingConfig config, @NotNull Collection<?extends Node> nodes) {
        Collection<Problem> problems = new ArrayList<>(1024);
        Consumer<Problem> collector = problems::add;
        lint(config, new ProblemReporter(collector), nodes);
        return problems;
    }

}
