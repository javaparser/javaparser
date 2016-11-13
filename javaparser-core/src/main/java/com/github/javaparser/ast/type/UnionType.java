package com.github.javaparser.ast.type;

import com.github.javaparser.Range;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * Represents a set of types. A given value of this type has to be assignable to at least one of the element types.
 * As of Java 8 it is only used in catch clauses.
 */
public class UnionType extends Type<UnionType> implements NodeWithAnnotations<UnionType> {

    private List<ReferenceType> elementsList;

    public UnionType(Range range, List<ReferenceType> elementsList) {
        super(range);
        setElementsList(elementsList);
    }

    public UnionType(List<ReferenceType> elementsList) {
        super();
        setElementsList(elementsList);
    }

    public List<ReferenceType> getElementsList() {
        return elementsList;
    }

    public void setElementsList(List<ReferenceType> elementsList) {
        if (this.elementsList != null) {
            for (ReferenceType element : elementsList){
                element.setParentNode(null);
            }
        }
        this.elementsList = elementsList;
        setAsParentNodeOf(this.elementsList);
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
