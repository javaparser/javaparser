package com.github.javaparser.ast;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/12/21)
 */
public class AbstractModifier extends Node{
    public AbstractModifier() {
        this(null);
    }

    protected AbstractModifier(TokenRange tokenRange) {
        super(tokenRange);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }
}
