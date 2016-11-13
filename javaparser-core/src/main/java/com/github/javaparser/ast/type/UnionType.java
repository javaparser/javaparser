package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Represents a set of types. A given value of this type has to be assignable to at least one of the element types.
 * As of Java 8 it is only used in catch clauses.
 */
public class UnionType extends Type<UnionType> implements NodeWithAnnotations<UnionType> {

    private NodeList<ReferenceType<?>> elements;

    public UnionType(Range range, NodeList<ReferenceType<?>> elements) {
        super(range, new NodeList<>());
        setElements(elements);
    }

    public UnionType(NodeList<ReferenceType<?>> elements) {
        this(Range.UNKNOWN, elements);
    }

    public NodeList<ReferenceType<?>> getElements() {
        return elements;
    }

    public UnionType setElements(NodeList<ReferenceType<?>> elements) {
        notifyPropertyChange(ObservableProperty.ELEMENTS, this.elements, elements);
        this.elements = assertNotNull(elements);
        setAsParentNodeOf(this.elements);
        return this;
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }
}
