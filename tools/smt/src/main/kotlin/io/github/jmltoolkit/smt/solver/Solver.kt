package io.github.jmltoolkit.smt.solver

import java.io.IOException
import java.io.InputStreamReader
import java.io.PrintWriter
import java.util.concurrent.ForkJoinPool
import java.util.concurrent.ForkJoinTask

/**
 * @author Alexander Weigl
 * @version 1 (08.08.22)
 */
class Solver {
    fun runAsync(input: String): ForkJoinTask<SolverAnswer> {
        return ForkJoinPool.commonPool().submit<SolverAnswer> { run(input) }
    }

    @Throws(IOException::class)
    fun run(input: String): SolverAnswer {
        return run { writer: PrintWriter -> writer.println(input) }
    }

    @Throws(IOException::class)
    protected fun startSmtSolver(): Process {
        val pb = ProcessBuilder("sh", "-c", "z3 -smt2 -in")
        return pb.start()
    }

    @Throws(IOException::class)
    fun run(query: AppendableTo): SolverAnswer {
        val p = startSmtSolver()
        try {
            PrintWriter(p.outputStream).use { out ->
                InputStreamReader(p.inputStream).use {
                    query.appendTo(out)
                    out.close()
                    return SolverAnswer(SExprParser.parseAll(it))
                }
            }
        } finally {
            p.destroyForcibly()
        }
    }
}
