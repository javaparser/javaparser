package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (4/5/21)
 */
public class JmlMethodDeclaration extends JmlClassLevel {
    private MethodDeclaration methodDeclaration;

    public JmlMethodDeclaration() {
        this(null);
    }

    @AllFieldsConstructor
    public JmlMethodDeclaration(MethodDeclaration methodDeclaration) {
        this(null, methodDeclaration);
    }

    public JmlMethodDeclaration(TokenRange tokenRange, MethodDeclaration methodDeclaration) {
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
