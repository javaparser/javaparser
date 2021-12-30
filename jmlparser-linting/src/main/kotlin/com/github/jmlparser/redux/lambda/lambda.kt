package com.github.jmlparser.redux.lambda

import com.github.javaparser.Position
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration
import com.github.javaparser.ast.body.MethodDeclaration
import com.github.javaparser.ast.body.TypeDeclaration
import com.github.javaparser.ast.expr.Expression
import com.github.javaparser.ast.expr.LambdaExpr
import com.github.javaparser.ast.expr.ObjectCreationExpr
import com.github.javaparser.ast.stmt.BlockStmt
import com.github.javaparser.ast.stmt.ExpressionStmt
import com.github.javaparser.ast.stmt.ReturnStmt
import com.github.javaparser.ast.type.ClassOrInterfaceType
import com.github.javaparser.ast.visitor.ModifierVisitor
import com.github.javaparser.ast.visitor.Visitable

class LambdaReplacer(val nameGenerator: NameGenerator) : ModifierVisitor<Unit>() {
    override fun visit(n: LambdaExpr, arg: Unit?): Visitable {
        val decl: ClassOrInterfaceDeclaration = liftToInnerClass(n)
        val cu = n.findEnclosingType()
        require(cu != null) { "LambdaExpr is not enclosed in a type declaration" }
        cu.addMember(decl)
        return instantiate(decl)
    }

    private fun instantiate(decl: ClassOrInterfaceDeclaration): Expression {
        return ObjectCreationExpr(null, decl.toType(), NodeList())
    }

    private fun liftToInnerClass(lambdaExpr: LambdaExpr): ClassOrInterfaceDeclaration {
        val (interfazeName, method) = findSingleAbstractInterface(lambdaExpr)
        val name = nameGenerator.generate("__GENERATED_", lambdaExpr.range.orElse(null)?.begin)
        return ClassOrInterfaceDeclaration(NodeList(), false, name).also {
            it.addImplementedType(interfazeName)
            it.addMember(method)
        }
    }

    private fun findSingleAbstractInterface(lambdaExpr: LambdaExpr): Pair<String, MethodDeclaration> {
        val type: ClassOrInterfaceType? = assignToType(lambdaExpr)
        return if (type == null) {
            inferDefaultAbstractInterface(lambdaExpr)
        } else {
            type.nameAsString to MethodDeclaration()
        }
    }

    private fun inferDefaultAbstractInterface(lambdaExpr: LambdaExpr): Pair<String, MethodDeclaration> {
        var interfaze: String
        val md = MethodDeclaration()

        val body = lambdaExpr.body
        val returnType =
            when (body) {
                is BlockStmt -> {
                    val last = body.statements.last as? ReturnStmt
                    last?.expression?.map { it.calculateResolvedType().toString() }
                }
                is ExpressionStmt -> {
                    body.expression.calculateResolvedType().toString()
                }
                else -> {
                    null
                }
            }

        when (lambdaExpr.parameters.size) {
            0 ->
                if (returnType == null) {
                    interfaze = "Runnable"
                    md.setName("run")
                } else {
                    interfaze = "java.util.function.Supplier<$returnType>"
                    md.setName("accept")
                }
            1 -> {
                val firstParam = lambdaExpr.parameters.first.get().typeAsString
                if (returnType == null) {
                    interfaze = "java.util.function.Consumer<$firstParam>"
                    md.setName("get")
                } else {
                    interfaze = "java.util.function.Function<$firstParam, $returnType>"
                    md.setName("invoke")
                }
            }
            2 -> {
                val firstParam = lambdaExpr.parameters.first()?.typeAsString
                val secondParam = lambdaExpr.parameters[1].typeAsString
                if (returnType == null) {
                    interfaze = "java.util.function.Consumer<$firstParam>"
                    md.setName("get")
                } else {
                    interfaze = "java.util.function.BiFunction<$firstParam, $secondParam, $returnType>"
                    md.setName("invoke")
                }
            }
            else -> error("ASM could not be infered")
        }

        //TODO md.type = returnType
        lambdaExpr.parameters.forEach {
            md.addParameter(it.clone())
        }

        return interfaze to md
    }

    private fun assignToType(lambdaExpr: LambdaExpr): ClassOrInterfaceType? {
        val type = lambdaExpr.calculateResolvedType()
        println("TEST: $type")
        return null
    }
}

private fun ClassOrInterfaceDeclaration.toType() = ClassOrInterfaceType(null, this.name.asString())

fun Node.findEnclosingType(): TypeDeclaration<*>? {
    var cur = this
    while (cur !is TypeDeclaration<*>) {
        if (!cur.hasParentNode()) {
            return null
        }
        cur = cur.parentNode.get()
    }
    return cur
}

/**
 * generates names guaranteeing uniqueness in generated names by onw instance of NameGenerator
 */
class NameGenerator {
    private val generatedNames: MutableList<String> = mutableListOf()
    fun generate(prefix: String, pos: Position?) = generate(prefix, pos, null)

    private fun generate(prefix: String, pos: Position?, counter: Int? = null): String {
        val line = pos?.line
        var newName = "${prefix}L$line"
        if (counter != null) {
            newName += "_$counter"
        }
        if (generatedNames.contains(newName)) {
            return generate(prefix, pos, counter ?: (0 + 1))
        }
        generatedNames.add(newName)
        return newName
    }
}
