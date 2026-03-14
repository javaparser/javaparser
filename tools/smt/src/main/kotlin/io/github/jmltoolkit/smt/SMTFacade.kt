package io.github.jmltoolkit.smt

import com.github.javaparser.ast.expr.Expression
import io.github.jmltoolkit.smt.model.SExpr

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
object SMTFacade {
    fun toSmt(expr: Expression, smtLog: SmtQuery, useInt: Boolean): SExpr {
        val visitor = JmlExpr2Smt(
            smtLog, if (useInt) IntArithmeticTranslator(smtLog)
            else BitVectorArithmeticTranslator(smtLog)
        )
        return expr.accept(visitor, null)
    }
}
