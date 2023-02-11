package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.VisitorValidator;

public class MethodBodyHasNoContract extends VisitorValidator {
    @Override
    public void visit(MethodDeclaration n, ProblemReporter arg) {
        if (n.getBody().isPresent() && n.getBody().get().getContracts().isPresent()
                && !n.getBody().get().getContracts().get().isEmpty()
        ) {
            arg.report(n, "Body of method has a block contract.");
        }
        super.visit(n, arg);
    }
}
