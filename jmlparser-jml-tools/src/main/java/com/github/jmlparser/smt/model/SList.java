package com.github.jmlparser.smt.model;

import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.types.ResolvedType;

import java.io.PrintWriter;
import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
public class SList extends SExpr {
    private SExpr[] value;

    public SList(SmtType stype, ResolvedType javaType, SExpr... args) {
        this.smtType = stype;
        this.javaType = javaType;
        this.value = args;
        for (SExpr arg : args) {
            Objects.requireNonNull(arg);
        }
    }

    public SExpr[] getValue() {
        return value;
    }

    @Override
    public void appendTo(PrintWriter writer) {
        writer.write('(');
        for (int i = 0; i < value.length; i++) {
            value[i].appendTo(writer);
            if (i < value.length - 1)
                writer.write(' ');
        }
        writer.write(')');
    }

    public SExpr get(int i) {
        return value[i];
    }
}
