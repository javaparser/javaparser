package io.github.jmltoolkit.smt

import com.github.javaparser.ast.ArrayCreationLevel
import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.body.Parameter
import com.github.javaparser.ast.expr.*
import com.github.javaparser.ast.jml.NodeWithContracts
import com.github.javaparser.ast.jml.expr.*
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr.JmlDefaultBinder
import com.github.javaparser.ast.visitor.GenericVisitorAdapter
import io.github.jmltoolkit.smt.model.SAtom
import io.github.jmltoolkit.smt.model.SExpr
import io.github.jmltoolkit.smt.model.SmtType
import io.github.jmltoolkit.utils.JMLUtils
import java.math.BigInteger
import kotlin.jvm.optionals.getOrNull

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
class JmlExpr2Smt(private val smtLog: SmtQuery, val translator: ArithmeticTranslator) :
    GenericVisitorAdapter<SExpr, Any?>() {

    private val boundedVars = VariableStack()

    override fun visit(n: ArrayAccessExpr, arg: Any?): SExpr {
        val array = n.name.accept(this, arg)
        val index = n.index.accept(this, arg)
        val rtype = n.calculateResolvedType()
        val stypes = translator.getType(rtype)
        return termFactory.select(stypes, rtype, array, index)
    }

    override fun visit(n: ArrayCreationExpr, arg: Any?): SExpr? {
        if (n.initializer.isPresent)
            return n.initializer.get().accept(this, arg)

        val name = "anon_array_" + (++anonCnt)
        val rType = n.calculateResolvedType()
        val type = translator.getType(rType)
        smtLog.declareConst(name, type)
        val variable: SExpr = termFactory.variable(type, rType, name)
        val zero: SExpr = translator.makeInt(BigInteger.ZERO)
        val arrayLength: SExpr = translator.arrayLength(variable)

        val boundedVars = ArrayList<SExpr>()
        var accessLevel: SExpr = variable
        for (i in 0 until n.levels.size) {
            val level: ArrayCreationLevel = n.levels[i]
            if (i == 0) {
                if (level.dimension.isPresent) {
                    val length: SExpr = level.dimension.get().accept(this, arg)!!
                    smtLog.addAssert(termFactory.equality(arrayLength, length))
                } else {
                    smtLog.addAssert(termFactory.lessOrEquals(zero, arrayLength, true))
                }
            } else {
                if (level.dimension.isPresent) {
                    val length: SExpr = level.dimension.get().accept(this, arg)!!
                    smtLog.addAssert(
                        termFactory.forall(
                            boundedVars,
                            termFactory.equality(translator.arrayLength(accessLevel), length)
                        )
                    )
                } else {
                    smtLog.addAssert(
                        termFactory.forall(
                            boundedVars,
                            termFactory.lessOrEquals(zero, translator.arrayLength(accessLevel), true)
                        )
                    )
                }
            }
            boundedVars.add(termFactory.binder(SmtType.INT, "idx$i"))
            accessLevel = termFactory.select(
                SmtType.JAVA_OBJECT, null, accessLevel,
                termFactory.variable(SmtType.INT, null, "idx$i")
            )
        }
        return variable
    }

    override fun visit(n: ArrayInitializerExpr, arg: Any?): SExpr {
        val name = "anon_array_" + (++anonCnt)
        val seq = n.values.map { it.accept(this, arg) }
        val myType: SmtType.Array = SmtType.Array(SmtType.INT, seq.first().smtType!!)
        smtLog.declareConst(name, myType)
        val `var`: SExpr = termFactory.variable(myType, null, name)
        for (i in seq.indices) {
            smtLog.addAssert( //(store ary idx sub)
                termFactory.store(`var`, translator.makeInt(i.toLong()), seq[i])
            )
        }

        val zero: SExpr = translator.makeInt(0)
        val length: SExpr = translator.arrayLength(`var`)
        smtLog.addAssert(termFactory.equality(length, translator.makeInt(n.values.size.toLong())))
        return `var`
    }

    override fun visit(n: AssignExpr?, arg: Any?): SExpr? {
        return super.visit(n, arg)
    }

    override fun visit(n: BinaryExpr, arg: Any?): SExpr {
        val left = n.left.accept(this, arg)
        val right = n.right.accept(this, arg)
        return translator.binary(n.operator, left, right)
    }

    override fun visit(n: ThisExpr?, arg: Any?): SExpr {
        return termFactory.makeThis()
    }

    override fun visit(n: SuperExpr?, arg: Any?): SExpr {
        return termFactory.makeSuper()
    }

    override fun visit(n: NameExpr, arg: Any?): SExpr {
        val resolved = n.resolve()
        val rType = resolved.type
        val type: SmtType = translator.getType(rType)
        if (!isBound(n.nameAsString)) {
            smtLog.declareConst(n.nameAsString, type)
        }
        return termFactory.variable(type, rType, n.nameAsString)
    }

    private fun isBound(nameAsString: String): Boolean {
        return boundedVars.contains(nameAsString)
    }


    override fun visit(n: NullLiteralExpr?, arg: Any?): SExpr {
        return termFactory.makeNull()
    }

    override fun visit(n: BooleanLiteralExpr, arg: Any?): SExpr {
        return translator.makeBoolean(n.value)
    }

    override fun visit(n: CastExpr?, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: CharLiteralExpr, arg: Any?): SExpr {
        return translator.makeChar(n)
    }

    override fun visit(n: ClassExpr?, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: ConditionalExpr, arg: Any?): SExpr {
        return termFactory.ite(
            n.condition.accept(this, arg),
            n.thenExpr.accept(this, arg),
            n.elseExpr.accept(this, arg)
        )
    }

    override fun visit(n: DoubleLiteralExpr?, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: FieldAccessExpr, arg: Any?): SExpr {
        val scopeType = n.scope.calculateResolvedType()
        val javaType = n.calculateResolvedType()
        val stype: SmtType = translator.getType(javaType)
        val obj: SExpr = n.scope.accept(this, arg)

        if (n.nameAsString.equals("length") && scopeType.isArray) {
            return translator.arrayLength(obj)
        }

        return termFactory.fieldAccess(javaType, stype, n.nameAsString, obj)
    }

    override fun visit(n: InstanceOfExpr, arg: Any?): SExpr {
        val leftType = n.expression.calculateResolvedType()
        val rightType = n.type.resolve()

        //TODO weigl return leftType.asReferenceType()
        //Pattern matching
        return termFactory.makeTrue()
    }

    override fun visit(n: IntegerLiteralExpr, arg: Any?): SExpr {
        return translator.makeInt(n)
    }

    override fun visit(n: LongLiteralExpr, arg: Any?): SExpr {
        return translator.makeLong(n)
    }

    override fun visit(n: MethodCallExpr, arg: Any?): SExpr {
        val method = n.resolve()
        val variable: SExpr = translator.makeVar(method.returnType)
        val ast = method.toAst().getOrNull()
        if (ast is NodeWithContracts<*>) {
            val contract = JMLUtils.createJointContract(ast.contracts)
            //TODO weigl add assertion for the return variable
            //TODO weigl add assertion for each parameter
            // smtLog.addAssert();
        }
        return variable
    }

    private var anonCnt: Int = 0

    override fun visit(n: ObjectCreationExpr?, arg: Any?): SExpr {
        val name = "anon" + (++anonCnt)
        smtLog.declareConst(name, SmtType.JAVA_OBJECT)
        val `var`: SExpr = termFactory.variable(SmtType.JAVA_OBJECT, null, name)
        smtLog.addAssert(termFactory.nonNull(`var`))
        return `var`
    }

    override fun visit(n: StringLiteralExpr, arg: Any?): SExpr {
        return SAtom(SmtType.STRING, null, ("\"" + n.asString()).toString() + "\"")
    }

    override fun visit(n: UnaryExpr, arg: Any?): SExpr {
        return translator.unary(n.operator, n.expression.accept(this, arg))
    }

    override fun visit(n: LambdaExpr?, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: TypeExpr?, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: SwitchExpr?, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: TextBlockLiteralExpr, arg: Any?): SExpr {
        return SAtom(SmtType.STRING, null, ("\"" + n.asString()).toString() + "\"")
    }


    override fun visit(n: RecordPatternExpr, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: TypePatternExpr, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    override fun visit(n: JmlQuantifiedExpr, arg: Any?): SExpr? {
        return boundedVars.bind(n.variables) {
            when (n.binder as JmlDefaultBinder) {
                JmlDefaultBinder.FORALL -> {
                    val e: Expression =
                        if (n.expressions.size == 2
                        ) BinaryExpr(
                            n.expressions[0],
                            n.expressions[1],
                            BinaryExpr.Operator.IMPLICATION
                        )
                        else n.expressions[0]
                    e.setParentNode(n)
                    return@bind termFactory.forall(
                        translator.getVariable(n.variables),
                        e.accept(this, arg)
                    )
                }

                JmlDefaultBinder.EXISTS -> {
                    val e1: Expression =
                        if (n.expressions.size == 2
                        ) BinaryExpr(n.expressions[0], n.expressions[1], BinaryExpr.Operator.AND)
                        else n.expressions[0]
                    e1.setParentNode(n)
                    return@bind termFactory.forall(
                        translator.getVariable(n.variables),
                        e1.accept(this, arg)
                    )
                }

                JmlDefaultBinder.BSUM, JmlDefaultBinder.MIN, JmlDefaultBinder.MAX, JmlDefaultBinder.PRODUCT ->
                    return@bind translator.makeIntVar()

                else -> return@bind null
            }
        }
    }

    override fun visit(n: JmlLabelExpr, arg: Any?): SExpr {
        return n.expression.accept(this, arg)
    }

    override fun visit(n: JmlLetExpr, arg: Any?): SExpr {
        return boundedVars.bind(n.variables) {
            val vars = mutableListOf<SExpr>()
            for (variable in n.variables.variables) {
                vars.add(
                    termFactory.list(
                        null, SmtType.BOOL, variable.nameAsString,
                        variable.initializer.get().accept(this, arg)
                    )
                )
            }
            val body: SExpr = n.body.accept(this, arg)
            return@bind termFactory.let(vars, body)
        }
    }

    override fun visit(n: JmlMultiCompareExpr, arg: Any?): SExpr {
        return JMLUtils.unroll(n).accept(this, arg)
    }

    override fun visit(n: JmlBinaryInfixExpr, arg: Any?): SExpr {
        val left: SExpr = n.left.accept(this, arg)
        val right: SExpr = n.right.accept(this, arg)
        return termFactory.list(null, SmtType.BOOL, n.operator.identifier, left, right)
    }

    override fun visit(n: JmlTypeExpr?, arg: Any?): SExpr {
        return super.visit(n, arg)
    }

    companion object {
        private val termFactory: SmtTermFactory = SmtTermFactory
    }
}

internal class VariableStack {
    private val seq = ArrayList<String>(16)

    fun <T> bind(variables: VariableDeclarationExpr, block: () -> T): T {
        val curPosition = seq.size
        for (variable in variables.variables) seq.add(variable.nameAsString)
        val v = block()
        truncate(curPosition)
        return v
    }

    fun <T> bind(variables: NodeList<Parameter>, block: () -> T): T {
        val curPosition = seq.size
        for (variable in variables) seq.add(variable.nameAsString)
        val value = block()
        truncate(curPosition)
        return value
    }

    private fun truncate(curPosition: Int) {
        while (seq.size > curPosition) {
            seq.removeAt(seq.size - 1)
        }
    }

    fun contains(nameAsString: String): Boolean {
        return seq.contains(nameAsString)
    }
}
