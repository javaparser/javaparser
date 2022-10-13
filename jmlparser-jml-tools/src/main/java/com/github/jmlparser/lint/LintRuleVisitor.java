package com.github.jmlparser.lint;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
public abstract class LintRuleVisitor extends VoidVisitorAdapter<LintProblemReporter> implements LintRule {
    /**
     * A validator that uses a visitor for validation.
     * This class is the visitor too.
     * Implement the "visit" methods you want to use for validation.
     */
    @Override
    public void accept(Node node, LintProblemReporter problemReporter) {
        reset();
        node.accept(this, problemReporter);
    }

    protected void reset() {
    }
}
