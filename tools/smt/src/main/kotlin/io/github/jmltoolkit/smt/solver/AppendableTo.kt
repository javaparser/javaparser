package io.github.jmltoolkit.smt.solver

import java.io.PrintWriter

/**
 * @author Alexander Weigl
 * @version 1 (08.08.22)
 */
fun interface AppendableTo {
    fun appendTo(writer: PrintWriter)
}
