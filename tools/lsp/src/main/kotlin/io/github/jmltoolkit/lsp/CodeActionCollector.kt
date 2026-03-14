package io.github.jmltoolkit.lsp

import com.github.javaparser.ast.Node
import com.github.javaparser.ast.expr.Expression
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration
import com.github.javaparser.ast.jml.clauses.JmlSignalsClause
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr.JmlDefaultBinder
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt
import org.eclipse.lsp4j.CodeAction
import org.eclipse.lsp4j.CodeActionContext
import org.eclipse.lsp4j.Command
import org.eclipse.lsp4j.jsonrpc.messages.Either
import kotlin.jvm.optionals.getOrNull

/**
 * This visitor gathers actions, that can be executed on nodes within the given range.
 */
class CodeActionCollector(val context: CodeActionContext?, private val range: com.github.javaparser.Range) :
    ResultingVisitor<MutableList<Either<Command, CodeAction>>>() {
    override val result = arrayListOf<Either<Command, CodeAction>>()
    fun add(x: Command) = result.add(Either.forLeft(x))
    fun add(x: CodeAction) = result.add(Either.forRight(x))

    override fun visit(n: JmlExpressionStmt, arg: Unit?) {
        if (n.kind != JmlExpressionStmt.JmlStmtKind.SET && n.kind != JmlExpressionStmt.JmlStmtKind.HENCE_BY) {
            addWelldefinedCheck(n.expression)
        }
        super.visit(n, arg)
    }

    override fun visit(n: JmlSimpleExprClause, arg: Unit?) {
        addWelldefinedCheck(n.expression)
    }

    override fun visit(n: JmlSignalsClause, arg: Unit?) {
        addWelldefinedCheck(n.expression)
        super.visit(n, arg)
    }

    override fun visit(n: JmlClassExprDeclaration, arg: Unit?) {
        addWelldefinedCheck(n.invariant)
        super.visit(n, arg)
    }

    private fun addWelldefinedCheck(n: Expression): Boolean {
        /*if (inRange(n)) {
            return add(WellDefinednessCheck.createCodeAction(n))
        }*/
        return false
    }

    private fun inRange(n: Node): Boolean {
        return n.range.getOrNull()?.contains(range) ?: false
    }

    override fun visit(n: JmlQuantifiedExpr, arg: Unit?) {
        if (n.binder == JmlDefaultBinder.FORALL || n.binder == JmlDefaultBinder.EXISTS) {
            val ca = CodeAction("Add boundary")
            add(ca)
        }
    }
}
