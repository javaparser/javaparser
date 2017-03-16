package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;

/**
 * This validator validates according to Java 9 syntax rules.
 */
public class Java9Validator extends Validators {
    public Java9Validator() {
        super(
                new BaseJavaValidator(),
                new VisitorValidator() {
                    @Override
                    public void visit(Name n, ProblemReporter arg) {
                        validateIdentifier(n, n.getIdentifier(), arg);
                        super.visit(n, arg);
                    }

                    @Override
                    public void visit(SimpleName n, ProblemReporter arg) {
                        validateIdentifier(n, n.getIdentifier(), arg);
                        super.visit(n, arg);
                    }
                }
        );
    }

    private static void validateIdentifier(Node n, String id, ProblemReporter arg) {
        if (id.equals("_")) {
            arg.report(n, "'_' is a reserved keyword.");
        }
    }
}
