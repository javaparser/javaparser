package com.github.javaparser.ast.body;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ClassInvariantClauseMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class ClassInvariantClause extends JmlClassLevel implements NodeWithModifiers<ClassInvariantClause> {

    private NodeList<Modifier> modifiers;

    private Expression invariant;

    public ClassInvariantClause() {
    }

    @AllFieldsConstructor
    public ClassInvariantClause(NodeList<Modifier> modifiers, Expression invariant) {
        this.modifiers = modifiers;
        this.invariant = invariant;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getInvariant() {
        return invariant;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ClassInvariantClause setInvariant(final Expression invariant) {
        assertNotNull(invariant);
        if (invariant == this.invariant) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.INVARIANT, this.invariant, invariant);
        if (this.invariant != null)
            this.invariant.setParentNode(null);
        this.invariant = invariant;
        setAsParentNodeOf(invariant);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == invariant) {
            setInvariant((Expression) replacementNode);
            return true;
        }
        for (int i = 0; i < modifiers.size(); i++) {
            if (modifiers.get(i) == node) {
                modifiers.set(i, (Modifier) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ClassInvariantClause clone() {
        return (ClassInvariantClause) accept(new CloneVisitor(), null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ClassInvariantClause(TokenRange tokenRange, NodeList<Modifier> modifiers, Expression invariant) {
        super(tokenRange);
        setModifiers(modifiers);
        setInvariant(invariant);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ClassInvariantClause setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null)
            this.modifiers.setParentNode(null);
        this.modifiers = modifiers;
        setAsParentNodeOf(modifiers);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ClassInvariantClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.classInvariantClauseMetaModel;
    }
}
