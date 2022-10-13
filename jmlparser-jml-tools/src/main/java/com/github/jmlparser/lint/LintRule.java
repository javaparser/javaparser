package com.github.jmlparser.lint;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.Validator;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public interface LintRule {
    void accept(Node node, LintProblemReporter problemReporter);
}
