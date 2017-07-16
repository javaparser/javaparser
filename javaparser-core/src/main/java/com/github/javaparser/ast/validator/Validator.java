package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;

/**
 * A validator that can be run on a node to check for semantic errors.
 * It is fully up to the implementor how to do this.
 */
public interface Validator extends TypedValidator<Node> {
    /**
     * @param node the node that wants to be validated
     * @param problemReporter when found, validation errors can be reported here
     */
    void accept(Node node, ProblemReporter problemReporter);
}
