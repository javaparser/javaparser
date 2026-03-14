package io.github.jmltoolkit.jml2java

import com.github.javaparser.ast.Jmlish
import com.github.javaparser.ast.expr.BinaryExpr
import com.github.javaparser.ast.expr.Expression
import com.github.javaparser.ast.stmt.BlockStmt
import com.github.javaparser.ast.stmt.ForStmt
import com.github.javaparser.utils.Pair
import java.util.*

/**
 * Transformation of JML expressions into equivalent Java code.
 *
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
object Jml2JavaFacade {
    fun translate(expression: Expression?): Pair<BlockStmt, Expression?> {
        val j2jt = Jml2JavaTranslator()
        val result = BlockStmt()
        val e = j2jt.accept(expression, result)
        return Pair(result, e)
    }

    fun embeddLoopInvariant(stmt: ForStmt?): BlockStmt? {
        return null
    }

    fun containsJmlExpression(expression: Expression?): Boolean {
        val search = Stack<Expression?>()
        search.add(expression)

        while (!search.isEmpty()) {
            val e = search.pop()
            if (e is Jmlish) {
                return true
            }

            if (e is BinaryExpr) {
                if (e.operator == BinaryExpr.Operator.IMPLICATION) return true
                if (e.operator == BinaryExpr.Operator.RIMPLICATION) return true
                if (e.operator == BinaryExpr.Operator.EQUIVALENCE) return true
                if (e.operator == BinaryExpr.Operator.SUB_LOCK) return true
                if (e.operator == BinaryExpr.Operator.SUB_LOCKE) return true
                if (e.operator == BinaryExpr.Operator.SUBTYPE) return true
                if (e.operator == BinaryExpr.Operator.RANGE) return true
            }

            for (childNode in e!!.childNodes) {
                if (childNode is Expression) search.add(childNode)
            }
        }
        return false
    }
}
