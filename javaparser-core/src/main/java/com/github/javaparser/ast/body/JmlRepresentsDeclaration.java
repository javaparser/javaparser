package com.github.javaparser.ast.body;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * REPRESENTS
 * ( expr | id ASSIGN expr | id SUCH_THAT expr)
 * (COMMA ( expr | id ASSIGN expr | id SUCH_THAT expr) )*
 * ;
 *
 * @author Alexander Weigl
 * @version 1 (3/11/21)
 */
public class JmlRepresentsDeclaration
        extends BodyDeclaration<JmlRepresentsDeclaration>
        implements NodeWithModifiers<JmlRepresentsDeclaration> {
    private NodeList<Modifier> modifiers;


    @Override
    public NodeList<Modifier> getModifiers() {
        return null;
    }

    @Override
    public JmlRepresentsDeclaration setModifiers(NodeList<Modifier> modifiers) {
        return null;
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }
}
