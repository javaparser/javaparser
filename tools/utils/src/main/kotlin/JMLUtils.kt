package io.github.jmltoolkit.utils

import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.expr.BinaryExpr
import com.github.javaparser.ast.expr.BooleanLiteralExpr
import com.github.javaparser.ast.expr.Expression
import com.github.javaparser.ast.expr.SimpleName
import com.github.javaparser.ast.jml.clauses.JmlContract
import com.github.javaparser.ast.jml.expr.JmlMultiCompareExpr
import com.github.javaparser.ast.type.ArrayType
import com.github.javaparser.ast.type.ClassOrInterfaceType
import com.github.javaparser.ast.type.PrimitiveType
import com.github.javaparser.ast.type.Type
import com.github.javaparser.resolution.types.ResolvedArrayType
import com.github.javaparser.resolution.types.ResolvedPrimitiveType.*
import com.github.javaparser.resolution.types.ResolvedType

/**
 * @author Alexander Weigl
 * @version 1 (02.07.22)
 */
object JMLUtils {
    const val GENERATED_COMBINED: String = "_generated_combined_"

    @Suppress("unused")
    fun unroll(n: JmlMultiCompareExpr): Expression {
        val r: Expression =
            if (n.expressions.isEmpty()) {
                BooleanLiteralExpr(true)
            } else if (n.expressions.size == 1) {
                n.expressions[0]
            } else {
                var e: Expression? = null
                for (i in 0 until n.expressions.size - 1) {
                    val cmp = BinaryExpr(
                        n.expressions[i].clone(),
                        n.expressions[i + 1].clone(),
                        n.operators[i]
                    )
                    e = if (e == null) cmp else BinaryExpr(e, cmp, BinaryExpr.Operator.AND)
                }
                e!!
            }
        r.setParentNode(n.parentNode.orElse(null))
        return r
    }

    fun unroll(old: NodeList<JmlContract>) {
        if (old.isEmpty()) return
        val target: ArrayList<JmlContract> = ArrayList<JmlContract>(128)
        for (c in old) {
            target.addAll(unroll(c))
        }
        old.clear()
        old.addAll(target)
    }

    private fun unroll(c: JmlContract): List<JmlContract> {
        if (c.subContracts.isEmpty()) return listOf<JmlContract>(c)
        val seq= c.subContracts.stream()
            .flatMap { e -> unroll(e).stream() }
            .toList()
        for (sub in seq) {
            for (clause in c.clauses) {
                sub.clauses.add(clause.clone())
            }
        }
        return seq
    }

    @Suppress("unused")
    fun createJointContract(m: NodeList<JmlContract>): JmlContract {
        val find = m.stream()
            .filter { name ->
                name.name.map { simpleName -> simpleName.asString().equals(GENERATED_COMBINED) }
                    .orElse(false)
            }.findFirst()
        if (find.isPresent) return find.get()

        unroll(m)

        val contract = JmlContract()
        contract.setName(SimpleName(GENERATED_COMBINED))
        //TODO weigl combine all requires, ensures ... clauses
        m.add(contract)
        return contract
    }

    fun resolvedType2Type(type: ResolvedType): Type {
        if (type.isPrimitive) {
            val rType = type.asPrimitive()!!
            return PrimitiveType(
                when (rType) {
                    BYTE -> PrimitiveType.Primitive.BYTE
                    SHORT -> PrimitiveType.Primitive.SHORT
                    CHAR -> PrimitiveType.Primitive.CHAR
                    INT -> PrimitiveType.Primitive.INT
                    LONG -> PrimitiveType.Primitive.LONG
                    BOOLEAN -> PrimitiveType.Primitive.BOOLEAN
                    FLOAT -> PrimitiveType.Primitive.FLOAT
                    DOUBLE -> PrimitiveType.Primitive.DOUBLE
                }
            )
        }

        if (type.isArray) {
            val aType: ResolvedArrayType = type.asArrayType()
            return ArrayType(resolvedType2Type(aType.componentType))
        }

        if (type.isReferenceType) {
            val rType = type.asReferenceType()
            return ClassOrInterfaceType(rType.qualifiedName)
        }

        throw RuntimeException("Unsupported type")
    }
}
