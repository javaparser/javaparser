package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

/**
 * A validator that uses a visitor for validation.
 * This class is the visitor too.
 * Implement the "visit" methods you want to use for validation.
 */
public abstract class VisitorValidator extends VoidVisitorAdapter<ProblemReporter> implements Validator {
    @Override
    public void accept(Node node, ProblemReporter problemReporter) {
        node.accept(this, problemReporter);
    }
}
