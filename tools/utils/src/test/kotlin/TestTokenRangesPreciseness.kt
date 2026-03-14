import com.github.javaparser.GeneratedJavaParserConstants
import com.github.javaparser.TokenRange
import com.github.javaparser.ast.CompilationUnit
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.jml.NodeWithJmlTags
import com.github.javaparser.jml.JmlUtility
import com.google.common.collect.Streams
import com.google.common.truth.Truth
import io.github.jmltoolkit.utils.LineColumnIndex
import io.github.jmltoolkit.utils.TestWithJavaParser
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestFactory
import java.nio.file.Files
import java.nio.file.Paths
import java.util.stream.Stream

/**
 * @author Alexander Weigl
 * @version 1 (18.10.22)
 */
internal class TestTokenRangesPreciseness : TestWithJavaParser() {
    @Test
    fun lineColumnIndex() {
        val lci = LineColumnIndex(
            """
                Lorem ipsum dolor sit amet, consetetur sadipscing elitr, sed diam
                nonumy eirmod tempor invidunt ut labore et dolore magna aliquyam erat, sed diam voluptua.
                    At vero eos et accusam et justo duo dolores et ea rebum. Stet clita kasd gubergren, no sea
                  takimata sanctus est Lorem ipsum dolor sit amet. Lorem ipsum dolor sit amet,
                   consetetur sadipscing elitr, sed diam nonumy eirmod tempor invidunt ut labore
                 et dolore magna aliquyam erat, sed diam voluptua. At vero eos et accusam et justo 
                  duo dolores et ea rebum. Stet clita kasd gubergren, no sea takimata sanctus est 
                Lorem ipsum dolor sit amet.
                
                """.trimIndent()
        )


        Truth.assertThat(lci.substring(1, 1, 1, 5))
            .isEqualTo("Lorem")

        Truth.assertThat(lci.substring(2, 1, 2, 6))
            .isEqualTo("nonumy")

        Truth.assertThat(lci.substring(6, 18, 6, 25))
            .isEqualTo("aliquyam")
    }

    @TestFactory
    @Throws(Throwable::class)
    fun ihm(): Stream<DynamicTest> {
        val content =
            Files.readString(Paths.get("../examples/ihm/VerifiedIdentityHashMap.java"))
        val result = parser.parse(content)
        Assertions.assertTrue(result.isSuccessful)
        return testTokenRanges(result.result.get(), content)
    }


    @TestFactory
    @Throws(Throwable::class)
    fun test(): Stream<DynamicTest> {
        val content = Files.readString(Paths.get("src/test/kotlin/TokenTest.java"))
        val result = parser.parse(content)
        Assertions.assertTrue(result.isSuccessful)
        return testTokenRanges(result.result.get(), content)
    }

    private fun testTokenRanges(node: CompilationUnit, content: String): Stream<DynamicTest> {
        val lci = LineColumnIndex(content)
        return JmlUtility.getAllNodes(node)
            .filter { it: Node? -> it is NodeWithJmlTags<*> }
            .flatMap { it: Node -> checkTokenRange(lci, it) }
        //checkTokenRange(lci, node);
    }

    private fun checkTokenRange(lci: LineColumnIndex, it: Node): Stream<DynamicTest?> {
        val tr = it.tokenRange
        return tr.map { javaTokens: TokenRange -> checkTokenRange(lci, javaTokens) }
            .orElse(Stream.empty<DynamicTest?>())
    }

    private fun checkTokenRange(lci: LineColumnIndex, javaTokens: TokenRange): Stream<DynamicTest?> {
        return Streams.stream(javaTokens)
            .filter { it.kind != GeneratedJavaParserConstants.EOF }
            .map { javaToken ->
                DynamicTest.dynamicTest(javaToken.toString()) {
                    val substring = lci.substring(javaToken.range.get())
                    val text = javaToken.text
                    if (!(substring == "@" && text == " ")) {
                        Truth.assertThat(substring).isEqualTo(text)
                    }
                }
            }
    }
}
