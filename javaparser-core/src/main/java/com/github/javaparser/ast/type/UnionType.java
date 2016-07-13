package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

import static com.github.javaparser.Position.pos;

/**
 * Represents a set of types. A given value of this type has to be assignable to at least one of the element types.
 * As of Java 8 it is only used in catch clauses.
 */
public class UnionType extends Type {

    private List<ReferenceType> elements;

    /**
     * @deprecated prefer using Range objects.
     */
    @Deprecated
    public UnionType(int beginLine, int beginColumn, int endLine,
                     int endColumn, List<ReferenceType> elements) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), elements);
    }
    
    public UnionType(Range range, List<ReferenceType> elements) {
        super(range);
        setElements(elements);
    }

    public UnionType(List<ReferenceType> elements) {
        super();
        setElements(elements);
    }

    public List<ReferenceType> getElements() {
        return elements;
    }

    public void setElements(List<ReferenceType> elements) {
        if (this.elements != null) {
            for (ReferenceType element : elements){
                element.setParentNode(null);
            }
        }
        this.elements = elements;
        setAsParentNodeOf(this.elements);
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
