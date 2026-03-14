package mlpp

import com.github.javaparser.JavaParser
import com.github.javaparser.JavaToken
import com.github.javaparser.ParserConfiguration
import com.github.javaparser.TokenRange
import com.github.javaparser.ast.Node
import io.github.jmltoolkit.utils.Helper.findAllJmlContainers
import java.io.IOException
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

/**
 * @author Alexander Weigl
 * @version 1 (07.04.23)
 */
class FeatureExtractor {
    private val parser: JavaParser
    internal val out = PrintWriter("features.csv")

    init {
        val config = ParserConfiguration()
        config.setProcessJml(true)
        parser = JavaParser(config)
    }

    @Throws(IOException::class)
    fun extract(path: Path?) {
        val cu = parser.parse(path)
        if (cu.isSuccessful) {
            val nodes = findAllJmlContainers(cu.result.get())

            extractN(nodes)
        }
    }

    private fun extractN(nodes: List<Node>) {
        for (node in nodes) {
            val tokenRange = node.tokenRange
            tokenRange.ifPresent { javaTokens: TokenRange -> extract(javaTokens.begin, javaTokens.end) }
        }
    }

    private fun extract(begin: JavaToken, end: JavaToken) {
        var cur: JavaToken? = begin
        val seq = ArrayList<JavaToken>(1024)
        while (cur != null && cur !== end) {
            if (!cur.category.isWhitespaceOrComment) {
                seq.add(cur)
            }
            cur = cur.nextToken.orElse(null)
        }
        extract(seq)
    }

    private fun extract(seq: List<JavaToken>) {
        val iter = FillNull(seq.iterator())
        var prev2: JavaToken? = null
        var prev1: JavaToken? = null
        var cur: JavaToken? = iter.next()
        var next: JavaToken? = iter.next()
        while (cur != null) {
            val tokenid0 = getKind(cur)
            val tokenid1 = getKind(prev1)
            val tokenid2 = getKind(prev2)
            val tokenidn = getKind(next)

            val widthleft = 120 - cur.range.get().end.column

            val lineident = 0

            val followedByNewline = next != null && cur.range.get().end.line != next.range.get().begin.line
            val followedByIndent = next?.range?.get()?.begin?.column ?: 0


            out.format(
                "%d\t%d\t%d\t%d\t%d\t%d\t%s\t%d\n",
                tokenid0,
                tokenid1,
                tokenid2,
                tokenidn,
                widthleft,
                lineident,
                followedByNewline,
                followedByIndent
            )

            prev2 = prev1
            prev1 = cur
            cur = next
            next = if (next == null) null else iter.next()
        }
    }

    internal fun printHead() {
        out.format("tokenid0\ttokenid1\ttokenid2\ttokenidn\twidthleft\tlineident\tfollowed_by_newline\tfollowed_by_indent\n")
    }
}

private class FillNull(private val iter: Iterator<JavaToken>) : Iterator<JavaToken?> {
    override fun hasNext(): Boolean {
        return iter.hasNext()
    }

    override fun next(): JavaToken? {
        if (iter.hasNext()) return iter.next()
        return null
    }
}

private fun getKind(cur: JavaToken?): Int {
    if (cur == null) return -1
    return cur.kind
}

@Throws(IOException::class)
fun main(args: Array<String>) {
    val e = FeatureExtractor()
    e.printHead()
    for (arg in args) {
        Files.walk(Paths.get(arg)).forEach { it: Path? ->
            try {
                e.extract(it)
            } catch (ex: IOException) {
                ex.printStackTrace()
            }
        }
    }
    e.out.flush()
}
