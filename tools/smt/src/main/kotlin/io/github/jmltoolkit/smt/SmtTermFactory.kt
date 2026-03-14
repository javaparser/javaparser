package io.github.jmltoolkit.smt

import com.github.javaparser.resolution.types.ResolvedPrimitiveType.BOOLEAN
import com.github.javaparser.resolution.types.ResolvedPrimitiveType.INT
import com.github.javaparser.resolution.types.ResolvedType
import com.google.common.cache.Cache
import com.google.common.cache.CacheBuilder
import io.github.jmltoolkit.smt.model.SAtom
import io.github.jmltoolkit.smt.model.SExpr
import io.github.jmltoolkit.smt.model.SList
import io.github.jmltoolkit.smt.model.SmtType
import io.github.jmltoolkit.smt.model.SmtType.BitVec
import java.math.BigInteger

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
object SmtTermFactory {
    private val symbolAndValueCache: Cache<String, SAtom> = CacheBuilder.newBuilder().softValues().build()

    //region boolean operators
    fun and(vararg terms: SExpr): SExpr = and(terms.toList())
    fun and(seq: List<SExpr>): SExpr = fnApply(BOOLEAN, SmtType.BOOL, "and", seq)

    fun or(vararg terms: SExpr): SExpr = or(terms.toList())
    fun or(terms: List<SExpr>) = fnApply(BOOLEAN, SmtType.BOOL, "or", terms)

    fun impl(premise: SExpr, concl: SExpr): SExpr = fnApply(BOOLEAN, SmtType.BOOL, "=>", premise, concl)

    //endregion
    fun ite(cond: SExpr, then: SExpr, otherwise: SExpr): SExpr =
        fnApply(then.javaType!!, then.smtType!!, "ite", cond, then, otherwise)

    fun fnApply(javaType: ResolvedType?, smtType: SmtType, fn: String, arg: SExpr): SExpr =
        SList(smtType, javaType, listOf(symbol(fn), arg))

    private fun fnApply(javaType: ResolvedType?, smtType: SmtType, fn: String, arg1: SExpr, arg2: SExpr): SExpr =
        SList(smtType, javaType, listOf(symbol(fn), arg1, arg2))

    private fun fnApply(
        javaType: ResolvedType?,
        smtType: SmtType,
        fn: String,
        arg1: SExpr,
        arg2: SExpr,
        arg3: SExpr
    ): SExpr = SList(smtType, javaType, listOf(symbol(fn), arg1, arg2, arg3))

    private fun fnApply(javaType: ResolvedType?, smtType: SmtType, fn: String, args: List<SExpr>): SExpr {
        val nargs = mutableListOf<SExpr>(symbol(fn))
        nargs.addAll(args)
        return SList(smtType, javaType, nargs)
    }

    fun symbol(fn: String): SAtom = symbolAndValueCache.get(fn) { SAtom(SmtType.SYMBOL, null, fn) }

    fun forall(variables: List<SExpr>, formula: SExpr): SExpr =
        fnApply(BOOLEAN, SmtType.BOOL, "forall", list(variables), formula)

    fun exists(variables: List<SExpr>, formula: SExpr): SExpr =
        fnApply(BOOLEAN, SmtType.BOOL, "exists", list(variables), formula)


    fun list(javaType: ResolvedType, smtType: SmtType, symbol: SAtom, args: Array<SExpr>): SExpr {
        val nargs = mutableListOf<SExpr>()
        nargs.add(symbol)
        nargs.addAll(args)
        return SList(smtType, javaType, nargs)
    }

    //TODO weigl correct?
    fun list(variables: List<SExpr>): SExpr {
        return SList(null, null, listOf())
    }

    //region polymorphic operators
    fun bor(left: SExpr, right: SExpr): SExpr {
        if (isBool(left, right)) return or(left, right)
        if (isBv(left, right)) return bvor(left, right)
        return typeException()
    }


    fun add(left: SExpr, right: SExpr): SExpr {
        if (isInt(left, right)) return iadd(left, right)
        if (isBv(left, right)) return bvadd(left, right)
        return typeException()
    }

    fun subtract(left: SExpr, right: SExpr): SExpr {
        if (isInt(left, right)) return isubstract(left, right)
        if (isBv(left, right)) return bvsubstract(left, right)
        return typeException()
    }

    fun modulo(left: SExpr, right: SExpr, b: Boolean): SExpr {
        if (isInt(left, right)) return imodulo(left, right)
        if (isBv(left, right)) return bvmodulo(left, right)
        return typeException()
    }

    fun shiftLeft(left: SExpr, right: SExpr): SExpr {
        if (isBv(left, right)) return bvshiftLeft(left, right)
        return typeException()
    }


    fun shiftRight(left: SExpr, right: SExpr, sign: Boolean): SExpr {
        if (isBv(left, right)) return bvshiftRight(left, right, sign)
        return typeException()
    }

    fun lessOrEquals(left: SExpr, right: SExpr, sign: Boolean): SExpr {
        if (isInt(left, right)) return ilessOrEquals(left, right)
        if (isBv(left, right)) return bvlessOrEquals(left, right)
        return typeException("Could not handle types '%s <= %s'", left.smtType, right.smtType)
    }

    fun greaterOrEquals(left: SExpr, right: SExpr, b: Boolean): SExpr {
        if (isInt(left, right)) return igreaterOrEquals(left, right)
        if (isBv(left, right)) return bvgreaterOrEquals(left, right)
        return typeException()
    }

    fun lessThan(left: SExpr, right: SExpr): SExpr {
        if (isInt(left, right)) return ilessThan(left, right)
        if (isBv(left, right)) return bvlessThan(left, right)
        return typeException("Could not handle types '%s <%s'", left.smtType!!, right.smtType!!)
    }

    fun equiv(left: SExpr, right: SExpr): SExpr = fnApply(BOOLEAN, SmtType.BOOL, "=", left, right)

    fun not(expr: SExpr): SExpr {
        if (isBv(expr)) return bvnot(expr)
        if (isBool(expr)) return fnApply(BOOLEAN, SmtType.BOOL, "not", expr)
        return typeException()
    }


    fun xor(left: SExpr, right: SExpr): SExpr = fnApply(BOOLEAN, SmtType.BOOL, "xor", left, right)

    fun equality(left: SExpr, right: SExpr): SExpr = fnApply(BOOLEAN, SmtType.BOOL, "=", left, right)

    fun band(left: SExpr, right: SExpr): SExpr {
        if (isBool(left, right)) return and(left, right)

        if (isBv(left, right)) return bvand(left, right)

        return typeException()
    }


    private fun fnApplyToBool(symbol: String, left: SExpr, right: SExpr): SExpr =
        fnApply(BOOLEAN, SmtType.BOOL, symbol, left, right)

    fun greaterThan(left: SExpr, right: SExpr): SExpr {
        if (isInt(left, right)) return igreaterThan(left, right)
        if (isBv(left, right)) return bvgreaterThan(left, right)
        return typeException("Could not handle types '%s > %s'", left.smtType, right.smtType)
    }


    fun negate(sexpr: SExpr): SExpr {
        if (isBool(sexpr)) return not(sexpr)
        if (isBv(sexpr)) return bvnegate(sexpr)
        return typeException()
    }


    fun multiply(left: SExpr, right: SExpr): SExpr {
        if (isInt(left, right)) return imultiply(left, right)
        if (isBv(left, right)) return bvmultiply(left, right)
        return typeException()
    }

    fun divide(left: SExpr, right: SExpr, b: Boolean): SExpr {
        if (isInt(left, right)) return idivide(left, right)
        if (isBv(left, right)) return bvdivide(left, right)
        return typeException()
    }


    //endregion
    //region integer operations
    fun intValue(svalue: String): SAtom = symbolAndValueCache.get(svalue) { SAtom(SmtType.INT, INT, svalue) }

    fun intValue(value: Long): SAtom = intValue("" + value)

    fun intValue(value: BigInteger): SAtom = intValue("" + value)

    fun iadd(left: SExpr, right: SExpr): SExpr = fnApplyToInt("+", left, right)

    fun ilessThan(left: SExpr, right: SExpr): SExpr = fnApplyToBool("<", left, right)

    fun ilessOrEquals(left: SExpr, right: SExpr): SExpr = fnApplyToBool("<=", left, right)

    fun igreaterThan(left: SExpr, right: SExpr): SExpr = fnApplyToBool(">", left, right)

    fun igreaterOrEquals(left: SExpr, right: SExpr): SExpr = fnApplyToBool(">=", left, right)

    fun isubstract(left: SExpr, right: SExpr): SExpr = fnApplyToInt("-", left, right)

    fun imultiply(left: SExpr, right: SExpr): SExpr = fnApplyToInt("*", left, right)

    fun intType(): SExpr = symbol("Int")

    fun imodulo(left: SExpr, right: SExpr): SExpr = fnApplyToInt("mod", left, right)

    fun idivide(left: SExpr, right: SExpr): SExpr = fnApplyToInt("/", left, right)

    //endregion
    //region bit vectors
    fun bvor(left: SExpr, right: SExpr): SExpr = fnApplyToBV("bvor", left, right)

    fun bvnot(expr: SExpr): SExpr = fnApplyToBV("bvnot", expr)

    fun bvnegate(sexpr: SExpr): SExpr = fnApplyToBV("bvneg", sexpr)

    fun bvlessThan(left: SExpr, right: SExpr): SExpr = fnApplyToBool("bvslt", left, right)

    fun bvlessOrEquals(left: SExpr, right: SExpr): SExpr = fnApplyToBool("bvsle", left, right)

    fun bvgreaterThan(left: SExpr, right: SExpr): SExpr = fnApplyToBool("bvsgt", left, right)

    fun bvgreaterOrEquals(left: SExpr, right: SExpr): SExpr = fnApplyToBool("bvsge", left, right)

    fun bvshiftRight(left: SExpr, right: SExpr, sign: Boolean): SExpr =
        fnApplyToBV(if (sign) "bvashr" else "bvshr", left, right)

    fun bvshiftLeft(left: SExpr, right: SExpr): SExpr = fnApplyToBV("bvshl", left, right)

    fun bvand(left: SExpr, right: SExpr): SExpr = fnApplyToBV("bvand", left, right)

    fun bvadd(left: SExpr, right: SExpr): SExpr = fnApplyToBV("bvadd", left, right)

    private fun bvsubstract(left: SExpr, right: SExpr): SExpr = fnApplyToBV("bvsub", left, right)

    private fun bvmultiply(left: SExpr, right: SExpr): SExpr = fnApplyToBV("bvmul", left, right)

    private fun bvdivide(left: SExpr, right: SExpr): SExpr = fnApplyToBV("bvsdiv", left, right)

    private fun bvmodulo(left: SExpr, right: SExpr): SExpr = fnApplyToBV("bvsrem", left, right)

    private fun fnApplyToBV(symbol: String, left: SExpr): SExpr = fnApply(null, left.smtType!!, symbol, left)


    fun makeBitvector(width: Int, value: Long): SExpr = makeBitvector(width, BigInteger.valueOf(value))


    fun makeBitvector(width: Int, value: BigInteger): SExpr {
        val type = SmtType.getBitVec(width)
        return SList(
            type, null,
            listOf(
                SList(null, null, listOf(symbol("_"), symbol("int2bv"), symbol("" + width))),
                intValue(value)
            )
        )
    }


    fun bvType(width: Int): SExpr =
        SList(SmtType.TYPE, null, listOf(symbol("_"), symbol("BitVec"), intValue(width.toLong())))

    //endregion
    private fun isBool(sexpr: SExpr): Boolean = sexpr.smtType == SmtType.BOOL

    private fun isBool(left: SExpr, right: SExpr): Boolean = left.smtType === right.smtType && isBool(left)

    private fun isBv(left: SExpr, right: SExpr): Boolean = left.smtType === right.smtType && isBv(left)

    private fun isBv(left: SExpr): Boolean = left.smtType is BitVec

    private fun isInt(left: SExpr, right: SExpr): Boolean = left.smtType === right.smtType && isInt(left)

    private fun isInt(left: SExpr): Boolean = left.smtType === SmtType.INT

    private fun typeException(): SExpr {
        throw RuntimeException("Type mismatch!")
    }


    private fun fnApplyToInt(symbol: String, left: SExpr, right: SExpr): SExpr =
        fnApply(INT, SmtType.INT, symbol, left, right)

    private fun fnApplyToBV(symbol: String, left: SExpr, right: SExpr): SExpr =
        fnApply(null, left.smtType!!, symbol, left, right)


    fun fpType(width: Int): SExpr =
        SList(SmtType.TYPE, null, listOf(symbol("_"), symbol("FloatingPoint"), intValue(width.toLong())))

    fun arrayType(from: SExpr, to: SExpr): SExpr = SList(SmtType.TYPE, null, listOf(symbol("Array"), from, to))


    fun list(javaType: ResolvedType?, stype: SmtType, vararg args: Any): SExpr {
        val nargs = mutableListOf<SExpr>()
        for (i in args.indices) {
            val arg = args[i]
            nargs.add(
                when (arg) {
                    is SExpr -> arg
                    is String -> symbol(arg)
                    else -> typeException("Unhandled type %s", arg.javaClass)
                }
            )
        }
        return SList(stype, javaType, nargs)
    }

    fun makeTrue(): SExpr = makeBoolean(true)


    fun makeFalse(): SExpr = makeBoolean(false)

    fun makeBoolean(value: Boolean): SExpr {
        val v = if (value) "true" else "false"
        return symbolAndValueCache.get(v) { SAtom(SmtType.BOOL, BOOLEAN, v) }
    }

    fun makeInt(value: String): SExpr = intValue(value)

    fun makeNull(): SExpr = symbol("null")

    fun makeThis(): SExpr = symbol("this")

    fun makeSuper(): SExpr = symbol("super")

    fun boolType(): SExpr = symbol("Bool")

    fun javaObjectType(): SExpr = symbol("Object")

    fun type(type: SmtType): SExpr {
        if (type === SmtType.JAVA_OBJECT) return javaObjectType()
        if (type === SmtType.INT) return intType()
        if (type === SmtType.REAL) return realType()
        if (type === SmtType.FP32) return fpType(32)
        if (type === SmtType.FP64) return fpType(64)
        if (type === SmtType.BOOL) return boolType()
        if (type is SmtType.Array) return arrayType(
            type(type.from),
            type(type.to)
        )
        if (type is BitVec) return bvType(type.width)

        return typeException()
    }


    private fun realType(): SExpr = symbol("Int")

    fun variable(type: SmtType, javaType: ResolvedType?, name: String): SExpr =
        //nocache, conflict in type could be created
        SAtom(type, javaType, name)

    fun command(symbol: String, vararg args: SExpr): SExpr =
        fnApply(null, SmtType.COMMAND, symbol, args.toList())

    fun select(stype: SmtType, javaType: ResolvedType?, array: SExpr, index: SExpr): SExpr =
        list(javaType, stype, symbol("select"), array, index)

    fun store(array: SExpr, index: SExpr, value: SExpr): SExpr =
        list(array.javaType, array.smtType!!, symbol("store"), array, index, value)

    fun fieldAccess(javaType: ResolvedType?, stype: SmtType, field: String, obj: SExpr): SExpr =
        fnApply(javaType, stype, field, obj)

    private fun typeException(fmt: String, vararg args: Any?): SExpr {
        throw RuntimeException(String.format(fmt, *args))
    }

    fun let(vars: List<SExpr>, body: SExpr): SExpr = list(body.javaType, body.smtType!!, "let", list(vars), body)

    fun nonNull(expr: SExpr): SExpr = not(equality(expr, makeNull()))

    fun binder(type: SmtType, name: String): SExpr = list(null, SmtType.JAVA_OBJECT, name, type(type))
}
