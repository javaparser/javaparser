import com.github.javaparser.JavaParser
import com.github.javaparser.ParserConfiguration
import com.github.javaparser.Problem
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.expr.Expression
import com.github.javaparser.symbolsolver.JavaSymbolSolver
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver
import com.google.common.truth.Truth
import io.github.jmltoolkit.smt.SMTFacade
import io.github.jmltoolkit.smt.SmtQuery
import io.github.jmltoolkit.smt.model.SExpr
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.yaml.snakeyaml.Yaml
import java.io.PrintWriter
import java.io.StringWriter
import java.util.function.Consumer

data class ExprTestCase(
    val expr: String,
    val result: String? = null,
    val resultBv: String? = null,
    val resultInt: String? = null,
    val disabled: Boolean = false
) {
    constructor(m: Map<String, Any?>)
            : this(
        expr = m["expr"] as String,
        result = m["result"] as String?,
        resultInt = m["resultInt"] as String?,
        resultBv = m["resultBv"] as String?,
        disabled = m["disabled"] as? Boolean ?: false
    )

}

/**
 * @author Alexander Weigl
 * @version 1 (14.06.22)
 */
class SmtTest {
    private val parser: JavaParser
    private val parent: Node

    init {
        val config = ParserConfiguration()
        config.setSymbolResolver(JavaSymbolSolver(ClassLoaderTypeSolver(ClassLoader.getSystemClassLoader())))
        parser = JavaParser(config)

        val r = parser.parse(javaClass.getResourceAsStream("Test.java"))
        if (!r.isSuccessful) {
            r.problems.forEach(Consumer { x: Problem? -> System.err.println(x) })
            Assertions.fail<Any>("Error during parsing")
        }
        parent = r.result.get().getType(0)
    }


    @TestFactory
    fun smtTranslation(): List<DynamicTest> {
        javaClass.getResourceAsStream("expr.yaml").use { inputStream ->
            val yaml = Yaml()
            val obj: List<Map<String, Any>> = yaml.load(inputStream)
            return obj
                .map { ExprTestCase(it) }
                .filter { !it.disabled }
                .flatMap {
                    listOf(
                        DynamicTest.dynamicTest(it.expr + " int") {
                            it.resultInt?.let { r -> smtTranslation(it.expr, r, true) }
                        },
                        DynamicTest.dynamicTest(it.expr + " bv") {
                            it.resultBv?.let { r -> smtTranslation(it.expr, r, false) }
                        },
                        DynamicTest.dynamicTest(it.expr + " _") {
                            it.result?.let { r -> smtTranslation(it.expr, r, true) }
                        }
                    )
                }
        }
    }

    fun smtTranslation(input: String?, expected: String, useInt: Boolean) {
        val e = parser.parseJmlExpression<Expression>(input)
        if (!e.isSuccessful) {
            e.problems.forEach(Consumer { x: Problem? -> System.err.println(x) })
            Assertions.fail<Any>("Error during parsing")
        }
        val expr = e.result.get()
        expr.setParentNode(parent)
        val smtLog = SmtQuery()
        val actualExpr: SExpr = SMTFacade.toSmt(expr, smtLog, useInt)

        val sw = StringWriter()
        val pw = PrintWriter(sw)
        smtLog.appendTo(pw)
        actualExpr.appendTo(pw)
        val actual = sw.toString()
        Truth.assertThat(actual.trim { it <= ' ' }).isEqualTo(expected.trim { it <= ' ' })
    }
}
