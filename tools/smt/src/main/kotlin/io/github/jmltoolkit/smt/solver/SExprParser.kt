package io.github.jmltoolkit.smt.solver

import io.github.jmltoolkit.smt.model.SAtom
import io.github.jmltoolkit.smt.model.SExpr
import io.github.jmltoolkit.smt.model.SList
import java.io.IOException
import java.io.PushbackReader
import java.io.Reader
import java.io.StringReader
import java.util.function.Predicate

object SExprParser {
    @Throws(IOException::class)
    fun parse(input: String): SExpr? {
        return parse(StringReader(input))
    }

    @Throws(IOException::class)
    fun parse(reader: Reader): SExpr? {
        return parse(PushbackReader(reader))
    }

    @Throws(IOException::class)
    fun parse(reader: PushbackReader): SExpr? {
        val eof = (-1).toChar().code
        var c = peekChar(reader)
        if (c == eof) // end of input
            return null
        else if (c == '('.code) {
            consumeChar(reader) // consume '('
            val seq = arrayListOf<SExpr>()
            do {
                c = peekChar(reader)
                if (c == ')'.code) {
                    consumeChar(reader)
                    break
                }
                val child: SExpr = parse(reader) ?: throw IllegalArgumentException("List not closed.")
                seq.add(child)
            } while (true)
            return SList(null, null, listOf())
        } else if (Character.isDigit(c) || c == '-'.code) {
            return parseNumber(reader)
        } else if (Character.isAlphabetic(c) || c == ':'.code) {
            return parseSymbol(reader)
        } else if (c == '"'.code) {
            return parseString(reader)
        } else {
        }
        throw IllegalStateException(String.format("Unexpected character: %c (%d)", c, c))
    }

    @Throws(IOException::class)
    private fun parseString(reader: PushbackReader): SExpr {
        val symbol = StringBuilder("\"")
        consumeChar(reader)
        var c: Int
        do {
            c = reader.read()
            if (c == -1) throw RuntimeException("String literal early aborted")
            symbol.append(c.toChar())
        } while (c != '"'.code)
        return SAtom(null, null, symbol.toString())
    }

    @Throws(IOException::class)
    private fun consumeChar(reader: PushbackReader): Int {
        return reader.read()
    }

    @Throws(IOException::class)
    private fun peekChar(reader: PushbackReader): Int {
        consumeEmptiness(reader)
        val c = reader.read()
        reader.unread(c)
        return c
    }

    @Throws(IOException::class)
    private fun consumeEmptiness(reader: PushbackReader) {
        var c: Int
        do {
            consumeWhitespace(reader)
            consumeComment(reader)
            c = reader.read()
            reader.unread(c)
        } while (Character.isWhitespace(c) || c == ';'.code)
    }

    @Throws(IOException::class)
    private fun consumeWhitespace(reader: PushbackReader) {
        consumeUntil(reader) { x: Int? ->
            !Character.isWhitespace(
                x!!
            )
        }
    }

    @Throws(IOException::class)
    private fun consumeComment(reader: PushbackReader) {
        val c: Int = reader.read()
        if (c == ';'.code) {
            consumeUntil(reader) { x: Int -> x != '\n'.code }
        } else {
            reader.unread(c)
        }
    }

    @Throws(IOException::class)
    private fun consumeUntil(reader: PushbackReader, pred: Predicate<Int>): Int {
        var c: Int
        do {
            c = reader.read()
        } while (!pred.test(c) && c != -1)
        reader.unread(c)
        return c
    }

    @Throws(IOException::class)
    private fun parseNumber(reader: PushbackReader): SExpr {
        var num = 0
        var factor = 1
        var c: Int = reader.read()
        if (c == '-'.code) {
            factor = -1
        } else {
            reader.unread(c)
        }

        do {
            c = reader.read()
            if (c == -1) break
            if (c == ')'.code || Character.isWhitespace(c) || c == ':'.code) {
                reader.unread(c)
                break
            }
            if (Character.isDigit(c)) {
                num = (num * 10) + (c - '0'.code)
            } else {
                throw IllegalStateException("Given number is invalid. Char " + c.toChar() + " found")
            }
        } while (true)
        return SAtom(null, null, "" + (num * factor))
    }

    @Throws(IOException::class)
    private fun parseSymbol(reader: PushbackReader): SExpr {
        val symbol = StringBuilder()
        do {
            val c: Int = reader.read()
            if (c == -1) break
            if (c == ')'.code || Character.isWhitespace(c)) {
                reader.unread(c)
                break
            }
            symbol.append(c.toChar())
        } while (true)
        return SAtom(null, null, symbol.toString())
    }

    @Throws(IOException::class)
    fun parseAll(input: Reader): List<SExpr> {
        val r = PushbackReader(input)
        val exprs: MutableList<SExpr> = ArrayList(1024)
        var c: Int
        while ((r.read().also { c = it }) != -1) {
            r.unread(c)
            val sexpr: SExpr = parse(r) ?: break
            exprs.add(sexpr)
        }
        return exprs
    }
}
