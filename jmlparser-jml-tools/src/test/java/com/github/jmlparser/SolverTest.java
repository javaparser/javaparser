package com.github.jmlparser;

import com.github.jmlparser.smt.solver.Solver;
import com.github.jmlparser.smt.solver.SolverAnswer;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (08.08.22)
 */
class SolverTest {
    @Test
    void startZ3Mini() throws IOException, InterruptedException {
        Assumptions.assumeTrue(z3Installed());
        Solver s = new Solver();
        SolverAnswer result = s.run("(assert (= (* 2 3) 6)) (check-sat) (get-model) (exit)");
        result.expectSat()
                .consume();

    }

    private boolean z3Installed() throws IOException, InterruptedException {
        return new ProcessBuilder("sh", "-c", "which z3").start().waitFor() == 0;
    }
}
