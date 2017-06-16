package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;

/**
 * Stub validator for when no validation is wanted.
 */
public final class NoProblemsValidator implements Validator {
    @Override
    public void accept(Node node, ProblemReporter problemReporter) {
    }
}
