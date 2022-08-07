package com.github.jmlparser.smt.model;

import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.types.ResolvedType;

import java.io.PrintWriter;

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
public abstract class SExpr {
    ResolvedType javaType;
    SmtType smtType;

    public ResolvedType getJavaType() {
        return javaType;
    }

    public SmtType getSmtType() {
        return smtType;
    }

    public abstract void appendTo(PrintWriter writer);
}
