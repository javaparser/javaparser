package com.github.javaparser.ast.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.NonEmptyProperty;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlLetExpr extends Expression {
    @NonEmptyProperty
    private NodeList<Parameter> variables;
    private Expression body;

    @AllFieldsConstructor
    public JmlLetExpr(NodeList<Parameter> variables, Expression body) {
        this.variables = variables;
        this.body = body;
    }


    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }

    @Override
    public boolean hasParentNode() {
        return false;
    }
}
