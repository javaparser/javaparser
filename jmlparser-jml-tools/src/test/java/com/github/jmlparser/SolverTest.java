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
public class SolverTest {
    @Test
    void startZ3Mini() throws IOException {
        Assumptions.assumeTrue(z3Installed());
        Solver s = new Solver();
        SolverAnswer result = s.run("(assert (= (* 2 3) 6)) (check-sat) (get-model) (exit)");
        result.expectSat().consume();
    }

    private static Boolean z3Installed = null;

    public static boolean z3Installed() {
        if (z3Installed != null) return z3Installed;
        try {
            return z3Installed = new ProcessBuilder("sh", "-c", "which z3").start().waitFor() == 0;
        } catch (Exception e) {
        }
        return z3Installed = false;
    }
}
