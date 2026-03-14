package io.github.jmltoolkit.wd

import com.github.javaparser.ast.expr.*
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause
import com.github.javaparser.ast.jml.expr.JmlLabelExpr
import com.github.javaparser.ast.jml.expr.JmlLetExpr
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr
import com.github.javaparser.ast.jml.expr.JmlTypeExpr
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt
import com.github.javaparser.ast.visitor.GenericVisitorAdapter
import com.github.javaparser.ast.visitor.VoidVisitorAdapter
import io.github.jmltoolkit.smt.ArithmeticTranslator
import io.github.jmltoolkit.smt.JmlExpr2Smt
import io.github.jmltoolkit.smt.SmtQuery
import io.github.jmltoolkit.smt.SmtTermFactory
import io.github.jmltoolkit.smt.model.SExpr
import java.math.BigInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (14.06.22)
 */
class WDVisitor : VoidVisitorAdapter<Any?>() {
    override fun visit(n: JmlExpressionStmt, arg: Any?) {
        n.expression.accept<Any>(this, arg)
    }
}

class WDVisitorExpr(smtLog: SmtQuery, private val translator: ArithmeticTranslator) :
    GenericVisitorAdapter<SExpr, Any?>() {
    private val smtFormula: JmlExpr2Smt = JmlExpr2Smt(smtLog, translator)

    override fun visit(n: NameExpr, arg: Any?): SExpr {
        val name = n.nameAsString
        return when (name) {
            "\\result", "\\exception" -> term.makeTrue()
            else -> term.makeTrue()
        }
    }

    override fun visit(n: ArrayAccessExpr, arg: Any?): SExpr {
        return term.and(
            n.name.accept(this, arg),
            n.index.accept(this, arg)
        )
    }

    override fun visit(n: ArrayCreationExpr, arg: Any?): SExpr {
        //TODO
        return n.initializer.get().accept(this, arg)
    }

    override fun visit(n: ArrayInitializerExpr, arg: Any?): SExpr {
        val seq = n.values.map { it.accept(this, arg) }
        return term.and(seq)
    }

    override fun visit(n: AssignExpr, arg: Any?): SExpr {
        return term.makeFalse()
    }

    override fun visit(n: BinaryExpr, arg: Any?): SExpr {
        when (n.operator) {
            BinaryExpr.Operator.IMPLICATION -> {
                val be = BinaryExpr(
                    UnaryExpr(n.left, UnaryExpr.Operator.LOGICAL_COMPLEMENT),
                    n.right, BinaryExpr.Operator.OR
                )
                return be.accept(this, arg)
            }

            BinaryExpr.Operator.DIVIDE, BinaryExpr.Operator.REMAINDER -> {
                val fml = n.right.accept(smtFormula, arg)
                return term.and(
                    n.right.accept(this, arg),
                    n.left.accept(this, arg),
                    term.not(
                        translator.binary(
                            BinaryExpr.Operator.EQUALS,
                            fml, smtFormula.translator.makeInt(BigInteger.ZERO)
                        )
                    )
                )
            }

            else -> return term.and(
                n.right.accept(this, arg),
                n.left.accept(this, arg)
            )
        }
    }

    override fun visit(n: BooleanLiteralExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: CastExpr, arg: Any?): SExpr {
        //TODO Type-check?
        return n.expression.accept(this, arg)
    }

    override fun visit(n: CharLiteralExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: ClassExpr, arg: Any?): SExpr {
        return term.makeFalse()
    }

    override fun visit(n: DoubleLiteralExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: EnclosedExpr, arg: Any?): SExpr {
        return wd(n.inner)
    }

    override fun visit(n: FieldAccessExpr, arg: Any?): SExpr {
        return wd(n.scope)
    }

    override fun visit(n: InstanceOfExpr, arg: Any?): SExpr {
        return n.expression.accept(this, arg)
    }

    override fun visit(n: IntegerLiteralExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: StringLiteralExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: SuperExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: ThisExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: UnaryExpr, arg: Any?): SExpr {
        return n.expression.accept(this, arg)
    }

    override fun visit(n: LambdaExpr, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: MethodReferenceExpr, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: TypeExpr, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: SwitchExpr, arg: Any?): SExpr {
        return term.and(wd(n.selector))
    }

    override fun visit(n: TextBlockLiteralExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: RecordPatternExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: TypePatternExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: JmlQuantifiedExpr, arg: Any?): SExpr {
        /*The quantified-expression is well-defined iff the two sub-expressions are well-defined. For a quantifier Q*/
        val seq: List<SExpr> = n.expressions.map { it.accept(this, arg) }
        val r: Expression = n.expressions[0]
        val v: Expression = n.expressions[0]

        val args: List<SExpr> = ArrayList<SExpr>()

        if (JmlQuantifiedExpr.JmlDefaultBinder.CHOOSE == n.binder) {
            return term.and(
                term.forall(args, wd(r)),
                term.forall(args, term.impl(valueOf(r), wd(v))),
                term.exists(
                    args, term.and(
                        valueOf(r),
                        valueOf(v)
                    )
                )
            )
        }
        return term.and(
            term.forall(args, wd(r)),
            term.forall(args, term.impl(valueOf(r), wd(v)))
        )
    }

    private fun valueOf(e: Expression): SExpr {
        return e.accept(smtFormula, null)
    }

    private fun wd(e: Expression): SExpr {
        return e.accept(this, null)
    }

    override fun visit(n: JmlExpressionStmt, arg: Any?): SExpr {
        return wd(n.expression)
    }

    override fun visit(n: JmlLabelExpr, arg: Any?): SExpr {
        return wd(n.expression)
    }

    override fun visit(n: JmlLetExpr, arg: Any?): SExpr {
        return term.and(wd(n.body),  /* TODO  arguments */term.makeTrue())
    }

    override fun visit(n: JmlClassExprDeclaration, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: JmlTypeExpr, arg: Any?): SExpr {
        return term.makeTrue()
    }

    override fun visit(n: JmlMultiExprClause, arg: Any?) =
        term.and(n.expressions.map { e: Expression -> this.wd(e) })

    override fun visit(n: MethodCallExpr, arg: Any?): SExpr {
        val name = n.nameAsString
        when (name) {
            "\\old", "\\pre", "\\past" ->                 /* Well-definedness: The expression is well-defined if the first argument is well-defined
                   and any label argument names either a built-in label (§11.611.6) or an in-scope Java or
                   JML ghost label (S11.511.5).*/
                return n.arguments[0].accept(this, arg)

            "\\fresh" ->                 /* Well-definedness: The argument must be well-defined and non-null. The second argument,
                   if present, must be the identifier corresponding to an in-scope label or a built-in label. */
                return n.arguments[0].accept(this, arg)
        }
        val seq = n.arguments.map { it: Expression -> it.accept(this, arg) }
        return term.and(seq)
    }

    companion object {
        private val term: SmtTermFactory = SmtTermFactory
    }
}
