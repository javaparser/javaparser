package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * Every type followed by [...] gets wrapped in an DimensionedArrayType for each [...].
 */
public class DimensionedArrayType extends ArrayType {
    private Expression dimension;

    public DimensionedArrayType(Range range, Type type, Expression dimension, List<AnnotationExpr> annotations) {
        super(range, type, annotations);
        setDimension(dimension);
    }

    @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public void setDimension(Expression dimension) {
        this.dimension = dimension;
        setAsParentNodeOf(dimension);
    }

    public Expression getDimension() {
        return dimension;
    }
}
