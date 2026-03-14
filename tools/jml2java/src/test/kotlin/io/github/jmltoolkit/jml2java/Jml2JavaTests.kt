package io.github.jmltoolkit.jml2java

import com.github.javaparser.ParseResult
import com.github.javaparser.Problem
import com.github.javaparser.ast.expr.Expression
import com.github.javaparser.printer.DefaultPrettyPrinter
import com.google.common.truth.Truth
import io.github.jmltoolkit.utils.TestWithJavaParser
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.yaml.snakeyaml.Yaml
import java.io.IOException
import java.util.function.Consumer
import java.util.stream.Stream

/**
 * @author Alexander Weigl
 * @version 1 (04.10.22)
 */
class Jml2JavaTests : TestWithJavaParser() {
    @TestFactory
    @Throws(IOException::class)
    fun j2jTranslation(): Stream<DynamicTest> {
        javaClass.getResourceAsStream("/expr.yaml").use { inputStream ->
            val yaml = Yaml()
            val obj: List<Map<String, Any>> = yaml.load(inputStream)
            return obj.stream().map { m: Map<String, Any> ->
                val a = m["expr"] as String?
                val result = m["result"] as String?
                DynamicTest.dynamicTest(a) {
                    if (result != null) jml2JavaTranslation(a, result)
                }
            }
        }
    }

    private fun jml2JavaTranslation(input: String?, expected: String) {
        val e: ParseResult<Expression> = parser.parseJmlExpression(input)
        if (!e.isSuccessful) {
            e.problems.forEach(Consumer { x: Problem? -> System.err.println(x) })
            Assertions.fail<Any>("Error during parsing")
        }
        val expr = e.result.get()
        expr.setParentNode(parent)
        val actual = Jml2JavaFacade.translate(expr)

        val dpp = DefaultPrettyPrinter()
        val sblock = dpp.print(actual.a)
        val sexpr = dpp.print(actual.b)
        Truth.assertThat(trimAllWs("$sblock $sexpr"))
            .isEqualTo(trimAllWs(expected))
    }

    companion object {
        private fun trimAllWs(expected: String): String {
            return expected.replace("\\s+".toRegex(), " ").trim { it <= ' ' }
        }
    }
}
