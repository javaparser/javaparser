package io.github.jmltoolkit.smt

import io.github.jmltoolkit.smt.solver.*
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (08.08.22)
 */
class SolverTest {
    @Test
    @Throws(IOException::class)
    fun startZ3Mini() {
        Assumptions.assumeTrue(Z3.z3Installed())
        val s = Solver()
        val result = s.run("(assert (= (* 2 3) 6)) (check-sat) (get-model) (exit)")
        result.expectSat().consume()
    }
}
