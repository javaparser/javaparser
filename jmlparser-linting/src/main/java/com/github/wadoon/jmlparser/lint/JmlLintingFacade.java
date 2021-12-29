package com.github.wadoon.jmlparser.lint;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.Validators;

import java.util.Collection;
import java.util.ServiceLoader;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class JmlLintingFacade {
    public Validators getLinter(JmlLintingConfig config) {
        ServiceLoader<LintRule> loader = ServiceLoader.load(LintRule.class);
        Validators validators = new Validators();
        for (LintRule lintRule : loader) {
            if (!config.isDisabled(lintRule)) {
                validators.add(lintRule);
            }
        }
        return validators;
    }

    public void lint(JmlLintingConfig config, ProblemReporter reporter, Collection<? extends Node> nodes) {
        Validators linter = getLinter(config);
        nodes.forEach(it -> linter.accept(it, reporter));
    }
}
