package com.github.javaparser.ast.validator.chunks;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.VisitorValidator;

public class UnderscoreKeywordValidator extends VisitorValidator {
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

    private static void validateIdentifier(Node n, String id, ProblemReporter arg) {
        if (id.equals("_")) {
            arg.report(n, "'_' is a reserved keyword.");
        }
    }
}
