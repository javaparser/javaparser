package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * Every type followed by [] gets wrapped in an ArrayType for each [].
 */
public class ArrayType extends ReferenceType<ArrayType> implements NodeWithAnnotations<ArrayType>, NodeWithType<ArrayType> {
    private Type type;

    public ArrayType(Range range, Type type, List<AnnotationExpr> annotations) {
        super(range);
        setType(type);
        setAnnotations(annotations);
    }

    @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public ArrayType setType(final Type type) {
        this.type = type;
        setAsParentNodeOf(this.type);
        return this;
    }

}
