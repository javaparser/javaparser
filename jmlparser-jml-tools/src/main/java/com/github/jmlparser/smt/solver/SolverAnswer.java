package com.github.jmlparser.smt.solver;

import com.github.jmlparser.smt.model.SAtom;
import com.github.jmlparser.smt.model.SExpr;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.08.22)
 */
public class SolverAnswer {
    private final List<SExpr> answers;
    private int currentPos = 0;

    public SolverAnswer(List<SExpr> answers) {
        this.answers = answers;
    }

    public List<SExpr> getAnswers() {
        return answers;
    }

    public SolverAnswer expectSat() {
        return expectSymbol("sat");
    }

    public SolverAnswer expectUnsat() {
        return expectSymbol("unsat");
    }

    public SolverAnswer expectUnknown() {
        return expectSymbol("unknown");
    }

    public SolverAnswer expectSymbol(String symbol) {
        if (!isSymbol(symbol)) {
            throw new RuntimeException("Unexpected symbol");
        }
        return this;
    }

    public boolean isSymbol(String symbol) {
        return symbol.equals(((SAtom) peek()).getValue());
    }

    public SExpr peek() {
        return answers.get(currentPos);
    }

    public void consume() {
        currentPos++;
    }

    public List<String> consumeErrors() {
        List<String> seq = new ArrayList<>();
        while (currentPos < answers.size()) {
            if (isError()) {
                seq.add(getErrorMessage());
                consume();
            } else {
                break;
            }
        }
        return seq;
    }

    private String getErrorMessage() {
        return peek().asList().get(1).asSymbolValue();
    }

    private boolean isError() {
        try {
            return peek().asList().get(0).asSymbolValue().equals("error");
        } catch (ClassCastException e) {
            return false;
        }
    }

    @Override
    public String toString() {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        answers.forEach(a -> {
            a.appendTo(pw);
            pw.println();
        });
        return sw.toString();
    }
}
