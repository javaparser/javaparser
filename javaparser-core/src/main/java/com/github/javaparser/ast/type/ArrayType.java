package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * Every type followed by [] gets wrapped in an ArrayType for each [].
 */
public class ArrayType extends ReferenceType {
    public ArrayType(Range range, Type type, List<AnnotationExpr> annotations) {
        super(range, type, annotations);
    }

    @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

}
