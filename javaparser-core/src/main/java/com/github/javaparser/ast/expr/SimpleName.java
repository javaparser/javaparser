package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A name that consists of a single identifier.
 * In other words: it.does.NOT.contain.dots.
 * @see Name
 */
public class SimpleName extends Node {
    private String id;

    public SimpleName() {
        this(Range.UNKNOWN, "empty");
    }

    public SimpleName(final String id) {
        this(Range.UNKNOWN, id);
    }

    public SimpleName(Range range, final String id) {
        super(range);
        setId(id);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public final String getId() {
        return id;
    }

    public SimpleName setId(final String id) {
        this.id = assertNotNull(id);
        return this;
    }
}
