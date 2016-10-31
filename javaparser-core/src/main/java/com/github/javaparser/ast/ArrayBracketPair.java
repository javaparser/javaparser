package com.github.javaparser.ast;

import com.github.javaparser.Range;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * In, for example, <code>int[] a[];</code> there are two ArrayBracketPair objects,
 * one for the [] after int, one for the [] after a.
 */
public class ArrayBracketPair extends Node implements NodeWithAnnotations<ArrayBracketPair> {
    private NodeList<AnnotationExpr> annotations = new NodeList<>();

    public ArrayBracketPair() {
        this(Range.UNKNOWN, new NodeList<AnnotationExpr>());
    }

    public ArrayBracketPair(NodeList<AnnotationExpr> annotations) {
        this(Range.UNKNOWN, annotations);
    }

    public ArrayBracketPair(Range range, NodeList<AnnotationExpr> annotations) {
        super(range);
        setAnnotations(annotations);
    }

    @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
    }

    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public ArrayBracketPair setAnnotations(NodeList<AnnotationExpr> annotations) {
        setAsParentNodeOf(annotations);
        this.annotations = assertNotNull(annotations);
        return this;
    }
}
