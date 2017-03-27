package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;

/**
 * A validator that walks the whole tree, visiting every node.
 */
public class TreeVisitorValidator implements Validator {
    private final Validator validator;

    public TreeVisitorValidator(Validator validator) {
        this.validator = validator;
    }

    @Override
    public final void accept(Node node, ProblemReporter reporter) {
        validator.accept(node, reporter);
        for (Node child : node.getChildNodes()) {
            accept(child, reporter);
        }
    }
}
