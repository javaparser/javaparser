package com.github.javaparser.ast.body;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;
import java.util.function.Consumer;

import com.github.javaparser.ast.observer.ObservableProperty;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ClassInvariantClauseMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class ClassInvariantClause extends JmlBodyDeclaration {

    private Expression invariant;

    public ClassInvariantClause() {
        this(null);
    }

    @AllFieldsConstructor
    public ClassInvariantClause(Expression invariant) {
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

    @Override
    public boolean isClassInvariantClause() {
        return true;
    }

    @Override
    public ClassInvariantClause asClassInvariantClause() {
        return this;
    }

    @Override
    public Optional<ClassInvariantClause> toClassInvariantClause() {
        return Optional.of(this);
    }

    public void ifClassInvariantClause(Consumer<ClassInvariantClause> action) {
        action.accept(this);
    }

    public Expression getInvariant() {
        return invariant;
    }

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
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == invariant) {
            setInvariant((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public ClassInvariantClause clone() {
        return (ClassInvariantClause) accept(new CloneVisitor(), null);
    }

    @Override
    public ClassInvariantClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.classInvariantClauseMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public ClassInvariantClause(TokenRange tokenRange, Expression invariant) {
        super(tokenRange);
        setInvariant(invariant);
        customInitialization();
    }
}
