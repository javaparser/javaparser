package io.github.jmltoolkit.jml2java

import com.github.javaparser.ast.Modifier
import com.github.javaparser.ast.body.Parameter
import com.github.javaparser.ast.body.VariableDeclarator
import com.github.javaparser.ast.expr.*
import com.github.javaparser.ast.jml.expr.JmlLetExpr
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr
import com.github.javaparser.ast.stmt.*
import com.github.javaparser.ast.type.PrimitiveType
import com.github.javaparser.ast.type.VarType
import com.github.javaparser.ast.visitor.GenericVisitorAdapter
import com.github.javaparser.resolution.types.ResolvedType
import io.github.jmltoolkit.utils.JMLUtils
import io.github.jmltoolkit.utils.Pattern
import java.util.concurrent.atomic.AtomicInteger

/**
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
class Jml2JavaTranslator {
    private val counter = AtomicInteger()

    fun accept(e: Expression?, arg: BlockStmt): Expression? {
        if (Jml2JavaFacade.containsJmlExpression(e)) {
            return e!!.accept(Jml2JavaVisitor(), arg)
        }
        return e // createAssignmentAndAdd(e, arg);
    }

    private fun createAssignmentAndAdd(e: Expression, arg: BlockStmt): Expression {
        arg.addAndGetStatement(createAssignmentFor(e))
        return NameExpr(targetForAssignment)
    }

    private fun createAssignmentFor(e: Expression): Statement {
        val decl = VariableDeclarationExpr(
            VariableDeclarator(
                VarType(),
                newTargetForAssignment(), e
            )
        )
        decl.addModifier(Modifier.DefaultKeyword.FINAL)
        return ExpressionStmt(decl)
    }

    private val targetForAssignment: SimpleName
        get() = SimpleName("_gen_" + counter.get())

    private fun newTargetForAssignment(): SimpleName {
        counter.getAndIncrement()
        return targetForAssignment
    }

    fun findPredicate(n: JmlQuantifiedExpr): Expression {
        return n.expressions[n.expressions.size - 1]
    }

    fun findUpperBound(n: JmlQuantifiedExpr, variable: String): Expression? {
        if (n.expressions.size == 3) return n.expressions[1]

        val e = findBound(n)

        if (e is JmlMultiCompareExpr) {
            if (e.expressions.size == 3 &&
                (e.expressions[1] as? NameExpr)?.nameAsString == variable
            ) {
                if (e.operators[0] == BinaryExpr.Operator.LESS_EQUALS) return e.expressions[0]
                if (e.operators[0] == BinaryExpr.Operator.LESS) return BinaryExpr(
                    e.expressions[0],
                    IntegerLiteralExpr("1"),
                    BinaryExpr.Operator.PLUS
                )
                throw IllegalStateException()
            }
        }

        val ph: Expression = NameExpr("_")
        run {
            val be = BinaryExpr(NameExpr(variable), ph, BinaryExpr.Operator.GREATER_EQUALS)
            val pattern = Pattern(be)
            pattern.addPlaceholder(ph, "min")
            val result = pattern.find(n)
            if (result != null) return result["min"] as Expression?
        }

        run {
            val be = BinaryExpr(NameExpr(variable), ph, BinaryExpr.Operator.GREATER)
            val pattern = Pattern(be)
            pattern.addPlaceholder(ph, "min")
            val result = pattern.find(n)
            if (result != null) return BinaryExpr(
                result["min"] as Expression?,
                IntegerLiteralExpr("1"),
                BinaryExpr.Operator.PLUS
            )
        }

        run {
            val be = BinaryExpr(ph, NameExpr(variable), BinaryExpr.Operator.LESS_EQUALS)
            val pattern = Pattern(be)
            pattern.addPlaceholder(ph, "min")
            val result = pattern.find(n)
            if (result != null) return result["min"] as Expression?
        }

        run {
            val be = BinaryExpr(ph, NameExpr(variable), BinaryExpr.Operator.LESS)
            val pattern = Pattern(be)
            pattern.addPlaceholder(ph, "min")
            val result = pattern.find(n)
            if (result != null) return BinaryExpr(
                result["min"] as Expression?,
                IntegerLiteralExpr("1"),
                BinaryExpr.Operator.PLUS
            )
        }

        return null
    }

    private inner class Jml2JavaVisitor : GenericVisitorAdapter<Expression, BlockStmt>() {
        override fun visit(n: JmlQuantifiedExpr, arg: BlockStmt): Expression {
            if (n.binder === JmlQuantifiedExpr.JmlDefaultBinder.FORALL) return visitForall(n, arg)
            if (n.binder === JmlQuantifiedExpr.JmlDefaultBinder.EXISTS) return visitExists(n, arg)

            throw IllegalArgumentException("Unsupport quantifier " + n.binder)
        }

        private fun visitForall(n: JmlQuantifiedExpr, arg: BlockStmt): Expression {
            assert(n.variables.size == 1)
            val rvalue = newSymbol("result_")
            val highVar = newSymbol("high_")
            val predVar = newSymbol("pred_")

            arg.addAndGetStatement(
                ExpressionStmt(
                    VariableDeclarationExpr(
                        VariableDeclarator(
                            PrimitiveType(PrimitiveType.Primitive.BOOLEAN),
                            rvalue, BooleanLiteralExpr(true)
                        )
                    )
                )
            )

            val variable: Parameter = n.variables[0]
            val lowCode = Jml2JavaFacade.translate(findLowerBound(n, variable.nameAsString))
            arg.addAndGetStatement(
                ExpressionStmt(
                    VariableDeclarationExpr(
                        VariableDeclarator(
                            variable.type.clone(), variable.nameAsString
                        )
                    )
                )
            )
            lowCode.a!!.addAndGetStatement(
                ExpressionStmt(
                    AssignExpr(
                        NameExpr(variable.nameAsString), lowCode.b,
                        AssignExpr.Operator.ASSIGN
                    )
                )
            )
            arg.addAndGetStatement(lowCode.a)

            val highCode = Jml2JavaFacade.translate(findUpperBound(n, variable.nameAsString))
            arg.addAndGetStatement(
                ExpressionStmt(
                    VariableDeclarationExpr(
                        VariableDeclarator(
                            variable.type.clone(), highVar
                        )
                    )
                )
            )
            highCode.a!!.addAndGetStatement(
                ExpressionStmt(
                    AssignExpr(
                        NameExpr(highVar), highCode.b,
                        AssignExpr.Operator.ASSIGN
                    )
                )
            )
            arg.addAndGetStatement(highCode.a!!.clone())

            val predCode = Jml2JavaFacade.translate(findPredicate(n))

            val whileStmt = arg.addAndGetStatement(WhileStmt())
            val lessThanExpr = BinaryExpr(
                NameExpr(variable.nameAsString),
                NameExpr(highVar), BinaryExpr.Operator.LESS
            )
            whileStmt.setCondition(
                BinaryExpr(lessThanExpr, NameExpr(rvalue), BinaryExpr.Operator.AND)
            )
            val body = BlockStmt()

            body.addAndGetStatement(
                ExpressionStmt(
                    VariableDeclarationExpr(
                        VariableDeclarator(PrimitiveType(PrimitiveType.Primitive.BOOLEAN), predVar)
                    )
                )
            )
            predCode.a!!.addAndGetStatement(
                ExpressionStmt(
                    AssignExpr(
                        NameExpr(predVar), predCode.b,
                        AssignExpr.Operator.ASSIGN
                    )
                )
            )
            body.addAndGetStatement(predCode.a)

            val assignPred = ExpressionStmt(
                AssignExpr(
                    NameExpr(rvalue),
                    BooleanLiteralExpr(true), AssignExpr.Operator.ASSIGN
                )
            )
            body.addAndGetStatement(
                IfStmt(NameExpr(predVar), assignPred, null)
            )
            body.addAndGetStatement(highCode.a!!.clone())

            whileStmt.setBody(body)
            return NameExpr(rvalue)
        }

        private fun newSymbol(prefix: String): String {
            return prefix + counter.getAndIncrement()
        }

        private fun visitExists(n: JmlQuantifiedExpr, arg: BlockStmt): Expression {
            return UnaryExpr(visitForall(n, arg), UnaryExpr.Operator.LOGICAL_COMPLEMENT)
        }


        override fun visit(n: JmlLetExpr, arg: BlockStmt): Expression {
            val inner = BlockStmt()
            val target = newTargetForAssignment()
            val type: ResolvedType = n.body.calculateResolvedType()
            arg.addAndGetStatement<ExpressionStmt>(
                ExpressionStmt(
                    VariableDeclarationExpr(
                        JMLUtils.resolvedType2Type(type),
                        target.asString()
                    )
                )
            )
            inner.addAndGetStatement(ExpressionStmt(n.variables))
            val e = accept(n.body, inner)
            arg.addAndGetStatement(inner)
            inner.addAndGetStatement(AssignExpr(NameExpr(target.asString()), e, AssignExpr.Operator.ASSIGN))
            return NameExpr(target.asString())
        }

        override fun visit(n: BinaryExpr, arg: BlockStmt): Expression {
            val left = accept(n.left, arg)
            val right = accept(n.right, arg)
            return when (n.operator) {
                BinaryExpr.Operator.IMPLICATION -> BinaryExpr(
                    UnaryExpr(
                        EnclosedExpr(left),
                        UnaryExpr.Operator.LOGICAL_COMPLEMENT
                    ),
                    right,
                    BinaryExpr.Operator.OR
                )

                BinaryExpr.Operator.RIMPLICATION -> BinaryExpr(
                    left,
                    UnaryExpr(
                        EnclosedExpr(right),
                        UnaryExpr.Operator.LOGICAL_COMPLEMENT
                    ),
                    BinaryExpr.Operator.OR
                )

                BinaryExpr.Operator.EQUIVALENCE -> BinaryExpr(
                    left,
                    right,
                    BinaryExpr.Operator.EQUALS
                )

                BinaryExpr.Operator.SUBTYPE, BinaryExpr.Operator.SUB_LOCK, BinaryExpr.Operator.SUB_LOCKE -> throw IllegalArgumentException(
                    "Unsupported operators."
                )

                else -> createAssignmentAndAdd(
                    BinaryExpr(left, right, n.operator),
                    arg
                )
            }
        }

        override fun visit(n: ArrayAccessExpr, arg: BlockStmt): Expression {
            return super.visit(n, arg)
        }

        override fun visit(n: ArrayCreationExpr, arg: BlockStmt): Expression {
            return super.visit(n, arg)
        }

        override fun visit(n: ArrayInitializerExpr, arg: BlockStmt): Expression {
            return super.visit(n, arg)
        }

        override fun visit(n: AssignExpr, arg: BlockStmt): Expression {
            return super.visit(n, arg)
        }
    }

    companion object {
        fun findBound(n: JmlQuantifiedExpr): Expression {
            if (n.expressions.size == 2) return n.expressions[0]
            else
                if (n.expressions.size == 1 && n.expressions.first() is BinaryExpr)
                    return n.expressions.first()
            throw IllegalArgumentException("Could not determine bound.")
        }

        fun findLowerBound(n: JmlQuantifiedExpr, variable: String): Expression? {
            if (n.expressions.size == 3) return n.expressions[0]

            val e = findBound(n)

            if (e is JmlMultiCompareExpr) {
                if (e.expressions.size == 3 &&
                    (e.expressions[1] as? NameExpr)?.nameAsString == variable
                ) {
                    if (e.operators[0] == BinaryExpr.Operator.LESS_EQUALS) return e.expressions[0]
                    if (e.operators[0] == BinaryExpr.Operator.LESS) return BinaryExpr(
                        e.expressions[0], IntegerLiteralExpr("1"), BinaryExpr.Operator.PLUS
                    )
                    throw IllegalStateException()
                }
            }

            val ph: Expression = NameExpr("_")
            run {
                val be = BinaryExpr(NameExpr(variable), ph, BinaryExpr.Operator.GREATER_EQUALS)
                val pattern = Pattern(be)
                pattern.addPlaceholder(ph, "min")
                val result = pattern.find(n)
                if (result != null) return result["min"] as Expression?
            }

            run {
                val be = BinaryExpr(NameExpr(variable), ph, BinaryExpr.Operator.GREATER)
                val pattern = Pattern(be)
                pattern.addPlaceholder(ph, "min")
                val result = pattern.find(n)
                if (result != null) return BinaryExpr(
                    result["min"] as Expression?,
                    IntegerLiteralExpr("1"),
                    BinaryExpr.Operator.PLUS
                )
            }

            run {
                val be = BinaryExpr(ph, NameExpr(variable), BinaryExpr.Operator.LESS_EQUALS)
                val pattern = Pattern(be)
                pattern.addPlaceholder(ph, "min")
                val result = pattern.find(n)
                if (result != null) return result["min"] as Expression?
            }

            run {
                val be = BinaryExpr(ph, NameExpr(variable), BinaryExpr.Operator.LESS)
                val pattern = Pattern(be)
                pattern.addPlaceholder(ph, "min")
                val result = pattern.find(n)
                if (result != null) return BinaryExpr(
                    result["min"] as Expression?,
                    IntegerLiteralExpr("1"),
                    BinaryExpr.Operator.PLUS
                )
            }

            return null
        }
    }
}
