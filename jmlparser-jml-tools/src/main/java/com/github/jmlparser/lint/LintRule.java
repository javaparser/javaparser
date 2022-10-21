package com.github.jmlparser.lint;

import com.github.javaparser.ast.Node;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public interface LintRule {
    String HINT = "HINT";
    String WARN = "WARN";
    String ERROR = "ERROR";

    void accept(Node node, LintProblemReporter problemReporter);
}
