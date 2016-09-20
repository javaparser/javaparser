package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * TODO this javadoc is incomprehensible.
 * Every type followed by [] gets wrapped in an ArrayType for each [].
 */
public class ArrayType extends ReferenceType<ArrayType> implements NodeWithAnnotations<ArrayType> {
    private Type componentType;

    public ArrayType(Type componentType, List<AnnotationExpr> annotations) {
        setComponentType(componentType);
        setAnnotations(annotations);
    }

    public ArrayType(Range range, Type componentType, List<AnnotationExpr> annotations) {
        super(range);
        setComponentType(componentType);
        setAnnotations(annotations);
    }

    @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public Type getComponentType() {
        return componentType;
    }

    public ArrayType setComponentType(final Type type) {
        this.componentType = type;
        setAsParentNodeOf(this.componentType);
        return this;
    }

}
