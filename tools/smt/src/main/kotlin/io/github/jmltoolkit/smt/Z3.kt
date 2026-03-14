package io.github.jmltoolkit.smt

/**
 *
 * @author Alexander Weigl
 * @version 1 (28.01.24)
 */
object Z3 {
    private var z3Installed: Boolean? = null
    fun z3Installed(): Boolean {
        if (z3Installed != null) return z3Installed!!
        try {
            return (ProcessBuilder("sh", "-c", "which z3").start().waitFor() == 0).also { z3Installed = it }
        } catch (e: Exception) {
        }
        return false.also { z3Installed = it }
    }
}