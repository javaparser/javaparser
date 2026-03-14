package io.github.jmltoolkit.redux


import com.github.javaparser.Position
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.NodeList
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration
import com.github.javaparser.ast.body.MethodDeclaration
import com.github.javaparser.ast.body.TypeDeclaration
import com.github.javaparser.ast.expr.LambdaExpr
import com.github.javaparser.ast.expr.ObjectCreationExpr
import com.github.javaparser.ast.stmt.BlockStmt
import com.github.javaparser.ast.stmt.ExpressionStmt
import com.github.javaparser.ast.stmt.Statement
import com.github.javaparser.ast.type.ClassOrInterfaceType
import com.github.javaparser.utils.Pair
import io.github.jmltoolkit.utils.Helper

/**
 * Replaces lambda expression by an internal named class.
 *
 *
 * Code was donated by Carsten Czisky @ciskar
 */
class LambdaReplacer(private val nameGenerator: NameGenerator) : Transformer {
    override fun apply(a: Node): Node {
        return Helper.findAndApply(LambdaExpr::class.java, a) { expr: LambdaExpr -> this.rewriteLambda(expr) }
    }

    private fun rewriteLambda(expr: LambdaExpr): Node {
        val enclosingType = expr.getParentNodeOfType(
            TypeDeclaration::class.java
        )
        check(!enclosingType.isEmpty) { "LambdaExpr is not enclosed in a type declaration" }
        val decl = liftToInnerClass(expr)
        enclosingType.get().addMember(decl)
        return instantiate(decl)
    }


    private fun instantiate(decl: ClassOrInterfaceDeclaration): ObjectCreationExpr {
        val type = ClassOrInterfaceType(null, decl.nameAsString)
        return ObjectCreationExpr(null, type, NodeList())
    }

    private fun liftToInnerClass(lambdaExpr: LambdaExpr): ClassOrInterfaceDeclaration {
        val sai = findSingleAbstractInterface(lambdaExpr)
        val interfazeName = sai.a
        val method = sai.b
        val name = nameGenerator.generate("__GENERATED_", lambdaExpr.range.orElse(null).begin)
        val it = ClassOrInterfaceDeclaration(NodeList(), false, name)
        it.addImplementedType(interfazeName)
        it.addMember(method)
        return it
    }

    private fun findSingleAbstractInterface(lambdaExpr: LambdaExpr): Pair<String, MethodDeclaration> {
        val type = assignToType(lambdaExpr)
        return if (type == null) {
            inferDefaultAbstractInterface(lambdaExpr)
        } else {
            Pair(
                type.nameAsString,
                MethodDeclaration()
            )
        }
    }

    private fun inferDefaultAbstractInterface(lambdaExpr: LambdaExpr): Pair<String, MethodDeclaration> {
        var interfaze = ""
        val md = MethodDeclaration()

        val body = lambdaExpr.body
        var returnType: String? = null

        if (body is BlockStmt) {
            val last: Statement? = body.statements.lastOrNull()
            returnType = last?.let { it: Statement -> it.asReturnStmt().expression() }
                ?.calculateResolvedType()?.toString()
        }

        if (body is ExpressionStmt) {
            returnType = body.expression.calculateResolvedType().toString()
        }


        when (lambdaExpr.parameters.size) {
            0 -> {
                if (returnType == null) {
                    interfaze = "Runnable"
                    md.setName("run")
                } else {
                    interfaze = "java.util.function.Supplier<\$returnType>"
                    md.setName("accept")
                }
            }

            1 -> {
                val firstParam = lambdaExpr.parameters.firstOrNull()?.typeAsString
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
                    interfaze = "java.util.function.BiConsumer<$firstParam,$secondParam>"
                    md.setName("get")
                } else {
                    interfaze = "java.util.function.BiFunction<$firstParam, $secondParam, $returnType>"
                    md.setName("invoke")
                }
            }

            else -> throw IllegalStateException("ASM could not be infered")
        }
        //TODO md.type = returnType
        for (parameter in lambdaExpr.parameters) {
            md.addParameter(parameter.clone())
        }
        return Pair(interfaze, md)
    }

    private fun assignToType(lambdaExpr: LambdaExpr): ClassOrInterfaceType? {
        val type = lambdaExpr.calculateResolvedType()
        println("TEST: \$type")
        return null //TODO
    }
}

/**
 * generates names guaranteeing uniqueness in generated names by onw instance of NameGenerator
 */
class NameGenerator {
    private val generatedNames: MutableSet<String> = HashSet()

    fun generate(prefix: String, pos: Position?): String {
        return generate(prefix, pos, null)
    }

    private fun generate(prefix: String, pos: Position?, counter: Int?): String {
        val line = pos?.line
        var newName = prefix + "L" + line
        if (counter != null) {
            newName += "_$counter"
        }
        if (generatedNames.contains(newName)) {
            return generate(prefix, pos, if (counter != null) counter + 1 else 0)
        }
        generatedNames.add(newName)
        return newName
    }
}
