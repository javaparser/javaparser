package io.github.jmltoolkit.lint.rules

import com.github.javaparser.ast.expr.VariableDeclarationExpr
import com.github.javaparser.ast.jml.stmt.JmlGhostStmt
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration
import io.github.jmltoolkit.lint.LintProblemReporter
import io.github.jmltoolkit.lint.LintRuleVisitor

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
class OverridingLocalNamesInGhost : LintRuleVisitor() {
    private var inGhost = false

    override fun reset() {
        inGhost = false
    }

    override fun visit(n: JmlGhostStmt, arg: LintProblemReporter) {
        inGhost = true
        super.visit(n, arg)
        inGhost = false
    }

    override fun visit(n: VariableDeclarationExpr, arg: LintProblemReporter) {
        if (inGhost) {
            val s: JmlGhostStmt = n.findAncestor(JmlGhostStmt::class.java).get()
            for (variable in n.variables) {
                val name = variable.nameAsExpression
                name.setParentNode(s)
                val value = s.symbolResolver.resolveDeclaration(name, ResolvedValueDeclaration::class.java)
                name.setParentNode(null)
                if (value != null) {
                    arg.error(variable, "", "", "Variable %s already declared in Java.", variable.nameAsString)
                }
            }
        }
    }
}
