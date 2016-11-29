package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithIdentifier;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A name that consists of a single identifier.
 * In other words: it.does.NOT.contain.dots.
 * @see Name
 */
public class SimpleName extends Node implements NodeWithIdentifier<SimpleName> {
    private String identifier;

    public SimpleName() {
        this(null, "empty");
    }

    public SimpleName(final String identifier) {
        this(null, identifier);
    }

    public SimpleName(Range range, final String identifier) {
        super(range);
        setIdentifier(identifier);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public final String getIdentifier() {
        return identifier;
    }

    @Override
    public SimpleName setIdentifier(final String identifier) {
        notifyPropertyChange(ObservableProperty.ID, this.identifier, identifier);
        this.identifier = assertNotNull(identifier);
        return this;
    }
}
