package com.github.jmlparser.smt.solver;

import java.io.PrintWriter;

/**
 * @author Alexander Weigl
 * @version 1 (08.08.22)
 */
public interface AppendableTo {
    void appendTo(PrintWriter writer);
}
