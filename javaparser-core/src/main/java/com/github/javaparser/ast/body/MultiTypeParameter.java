package com.github.javaparser.ast.body;

import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

public class MultiTypeParameter extends BaseParameter {
    private List<Type> types;
	
    public MultiTypeParameter() {}

    public MultiTypeParameter(int modifiers, List<AnnotationExpr> annotations, List<Type> types, VariableDeclaratorId id) {
        super(modifiers, annotations, id);
        this.types = types;
    }

    public MultiTypeParameter(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers, List<AnnotationExpr> annotations, List<Type> types, VariableDeclaratorId id) {
        super(beginLine, beginColumn, endLine, endColumn, modifiers, annotations, id);
        this.types = types;
	}

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }
    
    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public List<Type> getTypes() {
        return types;
    }

    public void setTypes(List<Type> types) {
        this.types = types;
    }
}
