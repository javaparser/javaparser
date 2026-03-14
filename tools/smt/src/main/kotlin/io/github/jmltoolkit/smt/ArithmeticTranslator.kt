package io.github.jmltoolkit.smt

import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.body.Parameter
import com.github.javaparser.ast.expr.*
import com.github.javaparser.resolution.types.ResolvedType
import io.github.jmltoolkit.smt.model.SExpr
import io.github.jmltoolkit.smt.model.SmtType
import java.math.BigInteger

/**
 * @author Alexander Weigl
 * @version 1 (01.07.22)
 */
interface ArithmeticTranslator {
    fun binary(operator: BinaryExpr.Operator, left: SExpr, right: SExpr): SExpr

    fun makeChar(n: CharLiteralExpr): SExpr

    fun unary(operator: UnaryExpr.Operator, accept: SExpr): SExpr

    fun makeLong(n: LongLiteralExpr): SExpr

    fun makeInt(n: IntegerLiteralExpr): SExpr

    fun makeInt(i: BigInteger): SExpr

    fun makeIntVar(): SExpr

    fun getVariable(variables: NodeList<Parameter>): List<SExpr> {
        return variables.map { getVariable(it) }
    }

    fun getVariable(jmlBoundVariable: Parameter): SExpr

    fun makeBoolean(value: Boolean): SExpr

    fun getType(asPrimitive: ResolvedType): SmtType

    fun arrayLength(obj: SExpr): SExpr

    fun makeInt(i: Long): SExpr

    fun makeVar(rtype: ResolvedType): SExpr
}
