package io.github.jmltoolkit.smt

import com.github.javaparser.ast.body.Parameter
import com.github.javaparser.ast.expr.*
import com.github.javaparser.ast.expr.BinaryExpr.Operator.*
import com.github.javaparser.ast.expr.UnaryExpr.Operator.*
import com.github.javaparser.resolution.types.ResolvedArrayType
import com.github.javaparser.resolution.types.ResolvedPrimitiveType
import com.github.javaparser.resolution.types.ResolvedPrimitiveType.*
import com.github.javaparser.resolution.types.ResolvedType
import io.github.jmltoolkit.smt.model.SExpr
import io.github.jmltoolkit.smt.model.SmtType
import java.math.BigInteger

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
open class BitVectorArithmeticTranslator(val smtLog: SmtQuery) : ArithmeticTranslator {
    var cnt: Int = 0

    override fun binary(operator: BinaryExpr.Operator, left: SExpr, right: SExpr): SExpr =
        when (operator) {
            IMPLICATION -> term.impl(left, right)
            SUBTYPE -> error("")
            RANGE -> error("")
            SUB_LOCK -> error("")
            SUB_LOCKE -> error("")
            RIMPLICATION -> term.impl(right, left)
            EQUIVALENCE -> term.equiv(left, right)
            ANTIVALENCE -> term.not(term.equiv(left, right))
            OR -> term.or(left, right)
            AND -> term.and(left, right)
            BINARY_OR -> term.bor(left, right)
            BINARY_AND -> term.band(left, right)
            XOR -> term.xor(left, right)
            EQUALS -> term.equality(left, right)
            NOT_EQUALS -> term.not(term.equality(left, right))
            LESS -> term.lessThan(left, right)
            GREATER -> term.greaterThan(left, right)
            LESS_EQUALS -> term.lessOrEquals(left, right, true)
            GREATER_EQUALS -> term.greaterOrEquals(left, right, true)
            LEFT_SHIFT -> term.shiftLeft(left, right)
            SIGNED_RIGHT_SHIFT -> term.shiftRight(left, right, true)
            UNSIGNED_RIGHT_SHIFT -> term.shiftRight(left, right, true)
            BinaryExpr.Operator.PLUS -> term.add(left, right)
            BinaryExpr.Operator.MINUS -> term.subtract(left, right)
            MULTIPLY -> term.multiply(left, right)
            DIVIDE -> term.divide(left, right, true)
            REMAINDER -> term.modulo(left, right, true)
        }

    override fun makeChar(n: CharLiteralExpr): SExpr {
        return term.makeBitvector(16, n.value!![0].code.toLong())
    }

    override fun unary(operator: UnaryExpr.Operator, accept: SExpr) =
        when (operator) {
            UnaryExpr.Operator.PLUS, POSTFIX_INCREMENT, POSTFIX_DECREMENT -> accept
            UnaryExpr.Operator.MINUS -> term.negate(accept)
            PREFIX_INCREMENT -> term.add(accept, term.makeBitvector(32, 1))
            PREFIX_DECREMENT -> term.subtract(accept, term.makeBitvector(32, 1))
            LOGICAL_COMPLEMENT -> term.not(accept)
            BITWISE_COMPLEMENT -> term.not(accept)
        }

    override fun makeLong(n: LongLiteralExpr) = term.makeBitvector(64, n.value.toBigInteger())

    override fun makeInt(n: IntegerLiteralExpr) = term.makeBitvector(32, n.asNumber().toLong())

    override fun makeInt(i: BigInteger) = term.makeBitvector(32, i)

    override fun makeIntVar(): SExpr {
        val name = "__RAND_" + (++cnt)
        smtLog.declareConst(name, SmtType.BV32)
        return term.symbol(name)
    }

    override fun getVariable(jmlBoundVariable: Parameter): SExpr {
        val rType = jmlBoundVariable.type.resolve()
        return term.list(null, SmtType.BOOL, jmlBoundVariable.nameAsString, term.type(getType(rType)))
    }

    override fun makeBoolean(value: Boolean) = term.makeBoolean(value)

    override fun getType(asPrimitive: ResolvedType): SmtType {
        if (asPrimitive.isPrimitive) {
            val rType: ResolvedPrimitiveType = asPrimitive.asPrimitive()
            return getPrimitiveType(rType)
        }

        if (asPrimitive.isArray) {
            val aType: ResolvedArrayType = asPrimitive.asArrayType()
            val cType: SmtType = getType(aType.componentType)
            val intType: SmtType = getType(INT)
            return SmtType.Array(intType, cType)
        }

        if (asPrimitive.isReferenceType) {
            return SmtType.JAVA_OBJECT
        }

        throw RuntimeException("Unsupported type")
    }

    override fun arrayLength(obj: SExpr): SExpr {
        return term.list(INT, SmtType.BV32, term.symbol("bv\$length"), obj)
    }

    override fun makeInt(i: Long): SExpr {
        return makeInt(BigInteger.valueOf(i))
    }

    override fun makeVar(rtype: ResolvedType): SExpr {
        TODO("Not yet implemented")
    }

    open fun getPrimitiveType(rType: ResolvedPrimitiveType) =
        when (rType) {
            BOOLEAN -> SmtType.BOOL
            BYTE -> SmtType.BV8
            SHORT -> SmtType.BV16
            CHAR -> SmtType.BV16
            INT -> SmtType.BV32
            LONG -> SmtType.BV64
            FLOAT -> SmtType.FP32
            DOUBLE -> SmtType.FP64
        }

    companion object {
        private val term: SmtTermFactory = SmtTermFactory
    }
}
