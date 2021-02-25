package com.github.javaparser.ast.body;

import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class ClassInvariantClause extends JmlBodyDeclaration {

    public ClassInvariantClause() {
    }

    @Override
    public <R,A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }

}
