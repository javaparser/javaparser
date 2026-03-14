package io.github.jmltoolkit.utils

import com.github.javaparser.Position
import com.github.javaparser.Range

/**
 * The index is 1-based. The first character also begins in line 1 and column 1.
 *
 * @author Alexander Weigl
 * @version 1 (18.10.22)
 */
class LineColumnIndex(private val content: String) {
    var lineOffsets: IntArray =
        IntArray(1 + content.chars().filter { it: Int -> it == '\n'.code }.count().toInt())

    init {
        var cur = 1
        val chars = content.toCharArray()
        for (i in chars.indices) {
            if (chars[i] == '\n') lineOffsets[cur++] = i + 1
        }
    }

    fun substring(range: Range): String {
        return substring(range.begin, range.end)
    }

    private fun substring(begin: Position, end: Position): String {
        return substring(begin.line, begin.column, end.line, end.column)
    }

    fun substring(beginLine: Int, beginColumn: Int, endLine: Int, endColumn: Int): String {
        val a = positionToOffset(beginLine, beginColumn)
        val b = positionToOffset(endLine, endColumn)
        return content.substring(a, b + 1)
    }

    fun positionToOffset(p: Position): Int {
        return positionToOffset(p.line, p.column)
    }

    fun positionToOffset(line: Int, column: Int): Int {
        return lineOffsets[line - 1] + column - 1
    }
}
