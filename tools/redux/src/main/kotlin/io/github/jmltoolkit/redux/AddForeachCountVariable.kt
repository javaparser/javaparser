package io.github.jmltoolkit.redux

import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.expr.NameExpr
import com.github.javaparser.ast.expr.SimpleName
import com.github.javaparser.ast.expr.UnaryExpr
import com.github.javaparser.ast.expr.VariableDeclarationExpr
import com.github.javaparser.ast.jml.stmt.JmlGhostStmt
import com.github.javaparser.ast.stmt.BlockStmt
import com.github.javaparser.ast.stmt.ExpressionStmt
import com.github.javaparser.ast.stmt.ForEachStmt
import com.github.javaparser.ast.type.PrimitiveType
import io.github.jmltoolkit.utils.Helper

/**
 * @author Alexander Weigl
 * @version 1 (08.02.22)
 */
class AddForeachCountVariable : Transformer {
    override fun apply(a: Node): Node {
        return Helper.findAndApply(ForEachStmt::class.java, a) { forEachStmt: ForEachStmt ->
            addCountVariableInForeach(
                forEachStmt
            )
        }
    }

    companion object {
        const val VARIABLE_NAME_COUNT: String = "\\count"

        fun addCountVariableInForeach(forEachStmt: ForEachStmt): BlockStmt {
            val stmt = BlockStmt()
            forEachStmt.replace(stmt)
            val vdecl = VariableDeclarationExpr(PrimitiveType.intType(), VARIABLE_NAME_COUNT)
            val decl = JmlGhostStmt(NodeList<SimpleName>(), ExpressionStmt(vdecl))
            stmt.addStatement(decl)
            stmt.addStatement(forEachStmt)
            val loopBody = forEachStmt.body
            val increment = UnaryExpr(NameExpr(VARIABLE_NAME_COUNT), UnaryExpr.Operator.PREFIX_INCREMENT)
            if (loopBody.isBlockStmt) {
                (loopBody as BlockStmt).addStatement(0, increment)
            } else {
                val newLoopBody = BlockStmt()
                loopBody.replace(newLoopBody)
                newLoopBody.addStatement(increment)
                newLoopBody.addStatement(loopBody)
            }
            return stmt
        }
    }
}
