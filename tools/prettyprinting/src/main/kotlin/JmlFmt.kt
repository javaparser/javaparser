import com.google.common.base.CharMatcher
import com.google.common.base.Strings
import com.google.common.collect.ImmutableList
import com.google.common.collect.Range
import com.google.googlejavaformat.*
import com.google.googlejavaformat.java.*
import java.util.*
import java.util.regex.Pattern

/**
 *
 * @author Alexander Weigl
 * @version 1 (30.06.24)
 */
class JmlFmt {
    fun pp(x: String): String? {
        val input = JavaInput(x)
        val output = JavaOutput("\n", input, JmlCommentsHelper("\n", JavaFormatterOptions.defaultOptions()))
        val builder = OpsBuilder(input, output)
        builder.drain()
        val ops = builder.build()
        val doc = DocBuilder().withOps(ops).build()
        doc.computeBreaks(output.commentsHelper, 80, Doc.State(+0, 0))
        doc.write(output)
        output.flush()
        return output.getLine(0)
    }
}

class JmlCommentsHelper(
    private val lineSeparator: String,
    private val options: JavaFormatterOptions
) : CommentsHelper {
    private val javaCommentsHelper = JavaCommentsHelper(lineSeparator, options)

    override fun rewrite(tok: Input.Tok, maxWidth: Int, column0: Int): String {
        if (tok.isComment && tok.originalText.startsWith("/*@")) {
            var text = tok.originalText
            //TODO
            return text
        } else {
            return javaCommentsHelper.rewrite(tok, maxWidth, column0)
        }
    }

    // For non-javadoc-shaped block comments, shift the entire block to the correct
    // column, but do not adjust relative indentation.
    private fun preserveIndentation(lines: List<String>, column0: Int): String {
        val builder = StringBuilder()

        // find the leftmost non-whitespace character in all trailing lines
        var startCol = -1
        for (i in 1 until lines.size) {
            val lineIdx = CharMatcher.whitespace().negate().indexIn(lines[i])
            if (lineIdx >= 0 && (startCol == -1 || lineIdx < startCol)) {
                startCol = lineIdx
            }
        }

        // output the first line at the current column
        builder.append(lines[0])

        // output all trailing lines with plausible indentation
        for (i in 1 until lines.size) {
            builder.append(lineSeparator).append(Strings.repeat(" ", column0))
            // check that startCol is valid index, e.g. for blank lines
            if (lines[i].length >= startCol) {
                builder.append(lines[i].substring(startCol))
            } else {
                builder.append(lines[i])
            }
        }
        return builder.toString()
    }

    // Wraps and re-indents line comments.
    private fun indentLineComments(lines: List<String>, column0: Int): String {
        var lines = lines
        //lines = wrapLineComments(lines, column0)
        val builder = StringBuilder()
        builder.append(lines[0].trim { it <= ' ' })
        val indentString = Strings.repeat(" ", column0)
        for (i in 1 until lines.size) {
            builder.append(lineSeparator).append(indentString).append(lines[i].trim { it <= ' ' })
        }
        return builder.toString()
    }

    // Preserve special `//noinspection` and `//$NON-NLS-x$` comments used by IDEs, which cannot
    // contain leading spaces.
    val LINE_COMMENT_MISSING_SPACE_PREFIX: Pattern =
        Pattern.compile("^(//+)(?!noinspection|\\\$NON-NLS-\\d+\\$)[^\\s/]")

    // Remove leading whitespace (trailing was already removed), and re-indent.
    // Add a +1 indent before '*', and add the '*' if necessary.
    private fun indentJavadoc(lines: List<String>, column0: Int): String {
        val builder = StringBuilder()
        builder.append(lines[0].trim { it <= ' ' })
        val indent = column0 + 1
        val indentString = Strings.repeat(" ", indent)
        for (i in 1 until lines.size) {
            builder.append(lineSeparator).append(indentString)
            val line = lines[i].trim { it <= ' ' }
            if (!line.startsWith("*")) {
                builder.append("* ")
            }
            builder.append(line)
        }
        return builder.toString()
    }

    // Returns true if the comment looks like javadoc
    private fun javadocShaped(lines: List<String>): Boolean {
        val it = lines.iterator()
        if (!it.hasNext()) {
            return false
        }
        val first = it.next().trim { it <= ' ' }
        // if it's actually javadoc, we're done
        return first.startsWith("/*@") //TODO
    }
}