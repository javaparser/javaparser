package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.jml.clauses.JmlClause;
import com.github.javaparser.ast.jml.clauses.JmlClauseKind;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.jmlparser.lint.LintProblemReporter;
import com.github.jmlparser.lint.LintRuleVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class ContextSensitiveForbiddenFunctionsValidator extends LintRuleVisitor {
    public static final String MULTIPLE_SIGNALS_ONLY = "Use a single signals_only clause to avoid confusion";
    public static final String NOT_SPECIFIED_REDUNDANT = "This clause containing \\not_specified is redundant because you already specified it";
    public static final String BACKSLASH_RESULT_NOT_ALLOWED = "You can only use \\result in an ensures clause";
    public static final String OLD_EXPR_NOT_ALLOWED = "You can only use an \\old() expressions in ensures and signals clauses, assert and assume statements, and in loop invariants";
    private int signalsOnlyCounter;

    @Override
    public void visit(JmlContract n, LintProblemReporter arg) {
        signalsOnlyCounter = 0;
        reportMultipleSignalsOnlyClauses(n, arg);
    }

    private void reportMultipleSignalsOnlyClauses(JmlContract n, LintProblemReporter arg) {
        for (JmlClause clause : n.getClauses()) {
            if (clause.getKind() == JmlClauseKind.SIGNALS_ONLY)
                signalsOnlyCounter++;

            if (signalsOnlyCounter > 1) {
                arg.warn(clause, "", "", MULTIPLE_SIGNALS_ONLY);
            }
        }

        for (JmlContract subContract : n.getSubContracts()) {
            reportMultipleSignalsOnlyClauses(subContract, arg);
        }
    }
}
