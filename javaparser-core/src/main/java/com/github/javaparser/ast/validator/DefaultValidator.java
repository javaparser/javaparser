package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.stmt.TryStmt;

/**
 * The validator that is used by default by the static JavaParser methods.
 */
public class DefaultValidator extends Validators {
    public DefaultValidator() {
        super(new VisitorValidator() {
            @Override
            public void visit(TryStmt n, ProblemReporter reporter) {
                if (n.getCatchClauses().isEmpty()
                        && n.getResources().isEmpty()
                        && !n.getFinallyBlock().isPresent()) {
                    reporter.report("Try has no finally, no catch, and no resources", n);
                }
            }
        });
    }
}
