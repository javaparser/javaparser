package com.github.jmlparser.lint.rules

import com.github.javaparser.ast.jml.clauses.JmlClauseKind
import com.github.javaparser.ast.jml.clauses.JmlContract
import io.github.jmltoolkit.lint.LintProblemReporter
import io.github.jmltoolkit.lint.LintRuleVisitor

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
class ContextSensitiveForbiddenFunctionsValidator : LintRuleVisitor() {
    private var signalsOnlyCounter = 0

    override fun visit(n: JmlContract, arg: LintProblemReporter) {
        signalsOnlyCounter = 0
        reportMultipleSignalsOnlyClauses(n, arg)
    }

    private fun reportMultipleSignalsOnlyClauses(n: JmlContract, arg: LintProblemReporter) {
        for (clause in n.clauses) {
            if (clause.kind === JmlClauseKind.SIGNALS_ONLY) signalsOnlyCounter++

            if (signalsOnlyCounter > 1) {
                arg.warn(clause, "", "", MULTIPLE_SIGNALS_ONLY)
            }
        }

        for (subContract in n.subContracts) {
            reportMultipleSignalsOnlyClauses(subContract, arg)
        }
    }

    companion object {
        const val MULTIPLE_SIGNALS_ONLY: String = "Use a single signals_only clause to avoid confusion"
        const val NOT_SPECIFIED_REDUNDANT: String =
            "This clause containing \\not_specified is redundant because you already specified it"
        const val BACKSLASH_RESULT_NOT_ALLOWED: String = "You can only use \\result in an ensures clause"
        const val OLD_EXPR_NOT_ALLOWED: String =
            "You can only use an \\old() expressions in ensures and signals clauses, assert and assume statements, and in loop invariants"
    }
}
