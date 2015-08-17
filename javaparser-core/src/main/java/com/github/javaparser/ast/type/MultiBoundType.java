package com.github.javaparser.ast.type;

import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @since 3.0.0
 */
public class MultiBoundType extends Type {

    private List<ReferenceType> elements;

    public MultiBoundType(int beginLine, int beginColumn, int endLine,
                         int endColumn, List<ReferenceType> elements) {
        super(beginLine, beginColumn, endLine, endColumn);
        setElements(elements);
    }

    public List<ReferenceType> getElements() {
        return elements;
    }

    public MultiBoundType(List<ReferenceType> elements) {
        super();
        setElements(elements);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
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
}
