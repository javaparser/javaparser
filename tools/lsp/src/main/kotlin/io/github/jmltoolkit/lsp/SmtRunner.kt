package io.github.jmltoolkit.lsp

import java.io.File
import java.util.concurrent.CompletableFuture

/**
 *
 * @author Alexander Weigl
 * @version 1 (12.10.22)
 */
data class SmtResult(val out: String, val err: String, val exitCode: Int)
class SmtRunner(val z3Path: String) {
    constructor() : this(findZ3())

    fun retrieveVersion(): CompletableFuture<SmtResult> =
        CompletableFuture.supplyAsync {
            // z3 --version
            run("--version")
        }

    private fun run(vararg args: String): SmtResult {
        val seq = args.toMutableList()
        seq.add(0, z3Path)
        val process = ProcessBuilder(seq)
            .start()
        process.waitFor()
        return SmtResult(
            process.inputReader().readText(),
            process.errorReader().readText(),
            process.exitValue()
        )
    }

    fun executeSmt(smt: File): CompletableFuture<SmtResult> =
        CompletableFuture.supplyAsync {
            run("--smt2", smt.absolutePath)
        }

    fun executeSmt(smt: String): CompletableFuture<SmtResult> =
        CompletableFuture.supplyAsync {
            val f = File.createTempFile("jml-lsp", ".smt2")
            f.writeText(smt)
            f
        }.thenApply { executeSmt(it).get() }
}

private fun findZ3() = "z3"
