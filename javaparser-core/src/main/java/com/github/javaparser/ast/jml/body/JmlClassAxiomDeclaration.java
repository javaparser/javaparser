package com.github.javaparser.ast.jml.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/13/21)
 */
public class JmlClassAxiomDeclaration extends JmlClassLevel<JmlClassAccessibleDeclaration>
        implements NodeWithModifiers<JmlClassAxiomDeclaration> {
    NodeList<Modifier> modifiers;
    Expression expr;

    @AllFieldsConstructor
    public JmlClassAxiomDeclaration(NodeList<Modifier> modifiers, Expression expr) {
        this.modifiers = modifiers;
        this.expr = expr;
    }

    public JmlClassAxiomDeclaration(TokenRange range, NodeList<Modifier> modifiers, Expression expr) {
        super(range);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null;
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {

    }

    @Override
    public NodeList<Modifier> getModifiers() {
        return null;
    }

    @Override
    public JmlClassAxiomDeclaration setModifiers(NodeList<Modifier> modifiers) {
        return null;
    }

}
