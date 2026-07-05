package io.github.jmltoolkit.jml2java

import com.github.javaparser.ParseResult
import com.github.javaparser.ast.CompilationUnit
import com.github.javaparser.ast.expr.Expression
import com.github.javaparser.printer.DefaultPrettyPrinter
import com.github.javaparser.symbolsolver.JavaSymbolSolver
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver
import com.google.common.truth.Truth
import io.github.jmltoolkit.utils.TestWithJavaParser
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.yaml.snakeyaml.Yaml
import java.io.IOException

data class ExprTestCase(
    val expr: String,
    val result: String,
    val disabled: Boolean = false
) {
    constructor(m: Map<String, Any?>)
            : this(
        m["expr"] as String,
        m["result"] as String,
        m["disabled"] as? Boolean ?: false
    )

}


/**
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
class Jml2JavaTests : TestWithJavaParser() {
    val pseudoCompilationUnit = CompilationUnit().also {
        JavaSymbolSolver(ReflectionTypeSolver(true)).inject(it)
    }

    @TestFactory
    @Throws(IOException::class)
    fun j2jTranslation(): List<DynamicTest> {
        javaClass.getResourceAsStream("/expr.yaml").use { inputStream ->
            val yaml = Yaml()
            val obj: List<Map<String, Any>> = yaml.load(inputStream)
            println(obj)
            return obj.map { ExprTestCase(it) }
                .filter { !it.disabled }
                .map { DynamicTest.dynamicTest(it.expr) { jml2JavaTranslation(it) } }
        }
    }

    private fun jml2JavaTranslation(input: ExprTestCase) {
        val e: ParseResult<Expression> = parser.parseJmlExpression(input.expr)
        if (!e.isSuccessful) {
            e.problems.forEach { System.err.println(it) }
            error("Error during parsing")
        }
        val expr = e.result.get()
        expr.setParentNode(pseudoCompilationUnit)
        val actual = Jml2JavaFacade.translate(expr)

        val dpp = DefaultPrettyPrinter()
        val sblock = dpp.print(actual.a)
        val sexpr = dpp.print(actual.b)
        Truth
            .assertThat(trimAllWs("$sblock $sexpr"))
            .isEqualTo(trimAllWs(input.result))
    }
}

private fun trimAllWs(expected: String): String = expected.replace("\\s+".toRegex(), " ").trim { it <= ' ' }