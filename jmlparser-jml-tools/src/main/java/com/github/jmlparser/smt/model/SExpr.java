package com.github.jmlparser.smt.model;

import com.github.javaparser.resolution.types.ResolvedType;
import com.github.jmlparser.smt.solver.AppendableTo;
import org.jetbrains.annotations.Nullable;

import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * @author Alexander Weigl
 * @version 1 (07.08.22)
 */
public abstract class SExpr implements AppendableTo {
    @Nullable
    ResolvedType javaType;
    @Nullable
    SmtType smtType;

    @Nullable
    public ResolvedType getJavaType() {
        return javaType;
    }

    @Nullable
    public SmtType getSmtType() {
        return smtType;
    }

    public SList asList() {
        return (SList) this;
    }

    public String asSymbolValue() {
        return ((SAtom) this).getValue();
    }

    @Override
    public String toString() {
        StringWriter sw = new StringWriter();
        appendTo(new PrintWriter(sw));
        return sw.toString();
    }

    /*public int asNumberValue() {
        return ((com.github.jmlparser.smt.SExpr.SNumber) this).value;
    }*/
}
