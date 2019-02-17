package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;

import static com.github.javaparser.utils.CodeGenerationUtils.f;

/**
 * Validates that identifiers are not keywords - this for the few keywords that the parser
 * accepts because they were added after Java 1.0.
 */
public class ReservedKeywordValidator extends VisitorValidator {
    private final String keyword;
    private final String error;

    ReservedKeywordValidator(String keyword) {
        this.keyword = keyword;
        error = f("'%s' cannot be used as an identifier as it is a keyword.", keyword);
    }

    @Override
    public void visit(Name n, ProblemReporter arg) {
        if (n.getIdentifier().equals(keyword)) {
            arg.report(n, error);
        }
        super.visit(n, arg);
    }

    @Override
    public void visit(SimpleName n, ProblemReporter arg) {
        if (n.getIdentifier().equals(keyword)) {
            arg.report(n, error);
        }
        super.visit(n, arg);
    }
}
