package io.github.jmltoolkit.smt.solver

import io.github.jmltoolkit.smt.model.SAtom
import io.github.jmltoolkit.smt.model.SExpr
import java.io.PrintWriter
import java.io.StringWriter
import java.util.function.Consumer

/**
 * @author Alexander Weigl
 * @version 1 (08.08.22)
 */
class SolverAnswer(private val answers: List<SExpr>) {
    private var currentPos = 0
    fun expectSat(): SolverAnswer {
        return expectSymbol("sat")
    }

    fun expectUnsat(): SolverAnswer {
        return expectSymbol("unsat")
    }

    fun expectUnknown(): SolverAnswer {
        return expectSymbol("unknown")
    }

    fun expectSymbol(symbol: String): SolverAnswer {
        if (!isSymbol(symbol)) {
            throw RuntimeException("Unexpected symbol")
        }
        return this
    }

    fun isSymbol(symbol: String): Boolean {
        return symbol == (peek() as SAtom).value
    }

    fun peek(): SExpr {
        return answers[currentPos]
    }

    fun consume() {
        currentPos++
    }

    fun consumeErrors(): List<String> {
        val seq: MutableList<String> = ArrayList()
        while (currentPos < answers.size) {
            if (isError) {
                seq.add(errorMessage)
                consume()
            } else {
                break
            }
        }
        return seq
    }

    private val errorMessage: String
        get() = peek().asList().get(1).asSymbolValue()

    private val isError: Boolean
        get() = try {
            peek().asList().get(0).asSymbolValue().equals("error")
        } catch (e: ClassCastException) {
            false
        }

    override fun toString(): String {
        val sw = StringWriter()
        val pw = PrintWriter(sw)
        answers.forEach(Consumer { a: SExpr ->
            a.appendTo(pw)
            pw.println()
        })
        return sw.toString()
    }
}
