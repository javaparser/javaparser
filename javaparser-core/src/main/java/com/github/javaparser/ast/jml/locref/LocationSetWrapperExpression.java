package com.github.javaparser.ast.jml.locref;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (4/17/21)
 */
public class LocationSetWrapperExpression extends Expression {
    private NodeList<LocationSetExpression> expressions;

    public LocationSetWrapperExpression() {
    }

    @AllFieldsConstructor
    public LocationSetWrapperExpression(NodeList<LocationSetExpression> expressions) {
        this(null, expressions);
    }

    public LocationSetWrapperExpression(TokenRange tokenRange, NodeList<LocationSetExpression> expressions) {
        super(tokenRange);
        this.expressions = expressions;
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }
}
