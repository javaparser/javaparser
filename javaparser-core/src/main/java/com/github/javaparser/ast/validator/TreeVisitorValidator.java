package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;

/**
 * A validator that walks the whole tree, visiting every node.
 */
public abstract class TreeVisitorValidator implements Validator {
    @Override
    public final void accept(Node node, ProblemReporter reporter) {
        process(node, reporter);
        for (Node child : node.getChildNodes()) {
            accept(child, reporter);
        }
    }

    public abstract void process(Node node, ProblemReporter reporter);
}
