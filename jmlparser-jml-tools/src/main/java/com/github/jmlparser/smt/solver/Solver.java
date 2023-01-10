package com.github.jmlparser.smt.solver;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;

/**
 * @author Alexander Weigl
 * @version 1 (08.08.22)
 */
public class Solver {
    public ForkJoinTask<SolverAnswer> runAsync(String input) {
        return ForkJoinPool.commonPool().submit(() -> run(input));
    }

    public SolverAnswer run(String input) throws IOException {
        return run(writer -> writer.println(input));
    }

    protected Process startSmtSolver() throws IOException {
        ProcessBuilder pb = new ProcessBuilder("sh", "-c", "z3 -smt2 -in");
        return pb.start();
    }

    public SolverAnswer run(AppendableTo query) throws IOException {
        Process p = startSmtSolver();
        try (PrintWriter out = new PrintWriter(p.getOutputStream());
             Reader in = new InputStreamReader(p.getInputStream())) {
            query.appendTo(out);
            out.close();
            return new SolverAnswer(SExprParser.parseAll(in));
        } finally {
            p.destroyForcibly();
        }
    }
}
