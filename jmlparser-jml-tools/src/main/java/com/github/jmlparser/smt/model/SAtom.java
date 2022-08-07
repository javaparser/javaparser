package com.github.jmlparser.smt.model;

import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.types.ResolvedType;

import java.io.PrintWriter;

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
public class SAtom extends SExpr {
    private String value;

    public SAtom(SmtType stype, ResolvedType javaType, String value) {
        this.smtType = stype;
        this.javaType = javaType;
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    @Override
    public void appendTo(PrintWriter writer) {
        writer.write(value);
    }
}
