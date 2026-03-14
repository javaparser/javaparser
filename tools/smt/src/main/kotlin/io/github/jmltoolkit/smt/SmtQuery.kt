package io.github.jmltoolkit.smt

import io.github.jmltoolkit.smt.model.SExpr
import io.github.jmltoolkit.smt.model.SmtType
import io.github.jmltoolkit.smt.solver.AppendableTo
import java.io.PrintWriter
import java.io.StringWriter
import java.util.function.Consumer

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
class SmtQuery : AppendableTo {
    private val commands: MutableList<SExpr> = ArrayList(1024)
    private val variableStack: MutableList<MutableMap<String, SmtType>> = ArrayList()

    init {
        variableStack.add(HashMap())
    }

    fun declareConst(name: String, type: SmtType): Boolean {
        if (!declared(name)) {
            val a = term.list(
                null, SmtType.COMMAND,
                "declare-const", name, term.type(type)
            )
            commands.add(a)
            currentFrame[name] = type
            return true
        }
        return false
    }

    fun push() {
        variableStack.add(HashMap())
        commands.add(term.command("push"))
    }

    fun pop() {
        variableStack.remove(currentFrame)
        commands.add(term.command("pop"))
    }

    private fun declared(name: String): Boolean {
        return currentFrame.containsKey(name)
    }

    private val currentFrame
        get() = variableStack[variableStack.size - 1]

    override fun appendTo(writer: PrintWriter) {
        for (command in commands) {
            command.appendTo(writer)
            writer.println()
        }
    }


    fun defineThis() {
        declareConst("this", SmtType.JAVA_OBJECT)
        addAssert(term.nonNull(term.variable(SmtType.JAVA_OBJECT, null, "this")))
    }

    fun addAssert(nonNull: SExpr) {
        commands.add(term.command("assert", nonNull))
    }

    fun checkSat() {
        commands.add(term.command("check-sat"))
    }


    override fun toString(): String {
        val sw = StringWriter()
        val pw = PrintWriter(sw)
        commands.forEach(Consumer { a: SExpr ->
            a.appendTo(pw)
            pw.println()
        })
        return sw.toString()
    }

    companion object {
        private val term: SmtTermFactory = SmtTermFactory
    }
}
