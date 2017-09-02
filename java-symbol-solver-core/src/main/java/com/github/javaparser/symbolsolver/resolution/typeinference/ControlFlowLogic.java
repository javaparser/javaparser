package com.github.javaparser.symbolsolver.resolution.typeinference;

import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.BreakStmt;
import com.github.javaparser.ast.stmt.Statement;

/**
 *
 * See JLS 14.21
 *
 * Except for the special treatment of while, do, and for statements whose condition expression has the constant value
 * true, the values of expressions are not taken into account in the flow analysis.
 */
public class ControlFlowLogic {

    private static ControlFlowLogic instance = new ControlFlowLogic();

    public static ControlFlowLogic getInstance() {
        return instance;
    }

    private ControlFlowLogic() {

    }

    /**
     * A reachable break statement exits a statement if, within the break target, either there are no try statements
     * whose try blocks contain the break statement, or there are try statements whose try blocks contain the break
     * statement and all finally clauses of those try statements can complete normally.
     */
    public boolean exitTheStatement(BreakStmt breakStmt) {
        if (!isReachable(breakStmt)) {
            return false;
        }
        throw new UnsupportedOperationException();
    }

    // See JLS 14.21
    public boolean canCompleteNormally(Statement statement) {
        if (!isReachable(statement)) {
            return false;
        }
        if (statement instanceof BlockStmt) {
            BlockStmt blockStmt = (BlockStmt)statement;
            if (blockStmt.isEmpty()) {
                return true;
            }
            return canCompleteNormally(blockStmt.getStatement(blockStmt.getStatements().size() - 1));
        }
        // FIXME
        return true;
    }

    public boolean isReachable(Statement statement) {
        // FIXME
        return true;
    }


}
