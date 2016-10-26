package com.github.javaparser.ast;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * In <code>new int[1][2];</code> there are two ArrayCreationLevel objects,
 * the first one contains the expression "1",
 * the second the expression "2".
 */
public class ArrayCreationLevel extends Node implements NodeWithAnnotations<ArrayCreationLevel> {
    // TODO nullable
    private Expression dimension;
    private NodeList<AnnotationExpr> annotations = new NodeList<>();

    public ArrayCreationLevel(Range range, Expression dimension, NodeList<AnnotationExpr> annotations) {
        super(range);
        setDimension(dimension);
        setAnnotations(annotations);
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

    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public ArrayCreationLevel setAnnotations(NodeList<AnnotationExpr> annotations) {
        setAsParentNodeOf(annotations);
        this.annotations = assertNotNull(annotations);
        return this;
    }
}
