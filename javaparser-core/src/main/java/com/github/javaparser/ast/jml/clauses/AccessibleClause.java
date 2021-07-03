package com.github.javaparser.ast.jml.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.OptionalProperty;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class AccessibleClause extends JmlClause implements MethodContractable, BlockContractable, LoopContractable {

    private NodeList<SimpleName> heaps;

    private NodeList<Expression> exprs;

    @OptionalProperty
    private Expression measuredBy;

    public AccessibleClause() {
    }

    @AllFieldsConstructor
    public AccessibleClause(NodeList<SimpleName> heaps, NodeList<Expression> exprs, Expression measuredBy) {
        super();
        setHeaps(heaps);
        setExprs(exprs);
        setMeasuredBy(measuredBy);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public AccessibleClause(TokenRange tokenRange, NodeList<SimpleName> heaps, NodeList<Expression> exprs, Expression measuredBy) {
        super(tokenRange);
        setHeaps(heaps);
        setExprs(exprs);
        setMeasuredBy(measuredBy);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < exprs.size(); i++) {
            if (exprs.get(i) == node) {
                exprs.remove(i);
                return true;
            }
        }
        for (int i = 0; i < heaps.size(); i++) {
            if (heaps.get(i) == node) {
                heaps.remove(i);
                return true;
            }
        }
        if (measuredBy != null) {
            if (node == measuredBy) {
                removeMeasuredBy();
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
        for (int i = 0; i < exprs.size(); i++) {
            if (exprs.get(i) == node) {
                exprs.set(i, (Expression) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < heaps.size(); i++) {
            if (heaps.get(i) == node) {
                heaps.set(i, (SimpleName) replacementNode);
                return true;
            }
        }
        if (measuredBy != null) {
            if (node == measuredBy) {
                setMeasuredBy((Expression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public AccessibleClause clone() {
        return (AccessibleClause) accept(new CloneVisitor(), null);
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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public AccessibleClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getExprs() {
        return exprs;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public AccessibleClause setExprs(final NodeList<Expression> exprs) {
        assertNotNull(exprs);
        if (exprs == this.exprs) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSIONS, this.exprs, exprs);
        if (this.exprs != null)
            this.exprs.setParentNode(null);
        this.exprs = exprs;
        setAsParentNodeOf(exprs);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<SimpleName> getHeaps() {
        return heaps;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public AccessibleClause setHeaps(final NodeList<SimpleName> heaps) {
        assertNotNull(heaps);
        if (heaps == this.heaps) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.HEAPS, this.heaps, heaps);
        if (this.heaps != null)
            this.heaps.setParentNode(null);
        this.heaps = heaps;
        setAsParentNodeOf(heaps);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getMeasuredBy() {
        return Optional.ofNullable(measuredBy);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public AccessibleClause setMeasuredBy(final Expression measuredBy) {
        if (measuredBy == this.measuredBy) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MEASURED_BY, this.measuredBy, measuredBy);
        if (this.measuredBy != null)
            this.measuredBy.setParentNode(null);
        this.measuredBy = measuredBy;
        setAsParentNodeOf(measuredBy);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public AccessibleClause removeMeasuredBy() {
        return setMeasuredBy(null);
    }
}
