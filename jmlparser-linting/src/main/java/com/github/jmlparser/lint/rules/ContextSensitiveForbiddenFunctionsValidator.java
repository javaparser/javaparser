package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.validator.VisitorValidator;
import com.github.jmlparser.lint.LintRule;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class ContextSensitiveForbiddenFunctionsValidator extends VisitorValidator implements LintRule {
    public static final String MULTIPLE_SIGNALS_ONLY = "Use a single signals_only clause to avoid confusion";
    public static final String NOT_SPECIFIED_REDUNDANT = "This clause containing \\not_specified is redundant because you already specified it";
    public static final String BACKSLASH_RESULT_NOT_ALLOWED = "You can only use \\result in an ensures clause";
    public static final String OLD_EXPR_NOT_ALLOWED = "You can only use an \\old() expressions in ensures and signals clauses, assert and assume statements, and in loop invariants";
    @Override
    public void visit(NameExpr n, ProblemReporter arg) {
        super.visit(n, arg);
    }
}
