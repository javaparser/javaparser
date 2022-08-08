package com.github.jmlparser.smt;

import com.github.jmlparser.smt.model.SExpr;
import com.github.jmlparser.smt.model.SmtType;
import com.github.jmlparser.smt.solver.AppendableTo;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
public class SmtQuery implements AppendableTo {
    private static final SmtTermFactory term = SmtTermFactory.INSTANCE;

    private final List<SExpr> commands = new ArrayList<>(1024);

    private final List<Map<String, SmtType>> variableStack = new ArrayList<>();

    public SmtQuery() {
        variableStack.add(new HashMap<>());
    }

    public boolean declareConst(String name, SmtType type) {
        if (!declared(name)) {
            SExpr a = term.list(null, SmtType.COMMAND,
                    "declare-const", name, term.type(type));
            commands.add(a);
            getCurrentFrame().put(name, type);
            return true;
        }
        return false;
    }

    public void push() {
        variableStack.add(new HashMap<>());
        commands.add(term.command("push"));
    }

    public void pop() {
        variableStack.remove(getCurrentFrame());
        commands.add(term.command("pop"));
    }

    private boolean declared(String name) {
        return getCurrentFrame().containsKey(name);
    }

    private Map<String, SmtType> getCurrentFrame() {
        return variableStack.get(variableStack.size() - 1);
    }

    @Override
    public void appendTo(PrintWriter pw) {
        for (SExpr command : commands) {
            command.appendTo(pw);
            pw.println();
        }
    }


    public void defineThis() {
        declareConst("this", SmtType.JAVA_OBJECT);
        addAssert(term.nonNull(term.var(SmtType.JAVA_OBJECT, null, "this")));
    }

    public void addAssert(SExpr nonNull) {
        commands.add(term.command("assert", nonNull));
    }

    public void checkSat() {
        commands.add(term.command("check-sat"));
    }


    @Override
    public String toString() {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        commands.forEach(a -> {
            a.appendTo(pw);
            pw.println();
        });
        return sw.toString();
    }
}
