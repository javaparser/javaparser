package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (3/11/21)
 */
public class JmlFieldDeclaration extends JmlClassLevel {
    private FieldDeclaration decl;

    public JmlFieldDeclaration() {
    }

    @AllFieldsConstructor
    public JmlFieldDeclaration(FieldDeclaration decl) {
        this.decl = decl;
    }

    public JmlFieldDeclaration(TokenRange tokenRange, FieldDeclaration decl) {
        super(tokenRange);
        this.decl = decl;
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }
}
