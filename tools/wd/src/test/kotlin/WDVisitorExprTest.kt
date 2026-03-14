import com.github.javaparser.JavaParser
import io.github.jmltoolkit.smt.Z3
import io.github.jmltoolkit.wd.WdFacade.isWelldefined
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvFileSource

/**
 * @author Alexander Weigl
 * @version 1 (14.06.22)
 */
internal class WDVisitorExprTest {
    private val parser = JavaParser()

    @ParameterizedTest
    @CsvFileSource(resources = ["wd-expr.csv"], delimiterString = "§")
    fun wdExpression(expr: String) {
        Assumptions.assumeTrue(Z3.z3Installed())
        Assertions.assertTrue(isWelldefined(parser, expr))
    }

    @ParameterizedTest
    @CsvFileSource(resources = ["not-wd-expr.csv"], delimiterString = "§")
    fun wdExpressionError(expr: String) {
        Assumptions.assumeTrue(Z3.z3Installed())
        Assertions.assertFalse(isWelldefined(parser, expr))
    }
}
