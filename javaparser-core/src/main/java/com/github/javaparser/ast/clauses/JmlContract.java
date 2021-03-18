package com.github.javaparser.ast.clauses;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.JmlSpecification;
import com.github.javaparser.ast.stmt.Behavior;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlContractMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (3/14/21)
 */
public class JmlContract extends Node implements Jmlish {

    private Behavior behavior;

    private Modifier modifier;

    private NodeList<JmlClause> clauses = new NodeList<>();

    private NodeList<JmlContract> subContracts = new NodeList<>();

    public JmlContract() {
        super(null);
    }

    @AllFieldsConstructor
    public JmlContract(Behavior behavior, Modifier modifier, NodeList<JmlClause> clauses, NodeList<JmlContract> subContracts) {
        super(null);
        this.behavior = behavior;
        this.modifier = modifier;
        this.clauses = clauses;
        this.subContracts = subContracts;
    }

    public JmlContract(TokenRange tokenRange) {
        super(tokenRange);
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
    public Behavior getBehavior() {
        return behavior;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlContract setBehavior(final Behavior behavior) {
        assertNotNull(behavior);
        if (behavior == this.behavior) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BEHAVIOR, this.behavior, behavior);
        this.behavior = behavior;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlClause> getClauses() {
        return clauses;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlContract setClauses(final NodeList<JmlClause> clauses) {
        assertNotNull(clauses);
        if (clauses == this.clauses) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CLAUSES, this.clauses, clauses);
        if (this.clauses != null)
            this.clauses.setParentNode(null);
        this.clauses = clauses;
        setAsParentNodeOf(clauses);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Modifier getModifier() {
        return modifier;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlContract setModifier(final Modifier modifier) {
        assertNotNull(modifier);
        if (modifier == this.modifier) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIER, this.modifier, modifier);
        if (this.modifier != null)
            this.modifier.setParentNode(null);
        this.modifier = modifier;
        setAsParentNodeOf(modifier);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlContract> getSubContracts() {
        return subContracts;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlContract setSubContracts(final NodeList<JmlContract> subContracts) {
        assertNotNull(subContracts);
        if (subContracts == this.subContracts) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SUB_CONTRACTS, this.subContracts, subContracts);
        if (this.subContracts != null)
            this.subContracts.setParentNode(null);
        this.subContracts = subContracts;
        setAsParentNodeOf(subContracts);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < clauses.size(); i++) {
            if (clauses.get(i) == node) {
                clauses.remove(i);
                return true;
            }
        }
        for (int i = 0; i < subContracts.size(); i++) {
            if (subContracts.get(i) == node) {
                subContracts.remove(i);
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
        for (int i = 0; i < clauses.size(); i++) {
            if (clauses.get(i) == node) {
                clauses.set(i, (JmlClause) replacementNode);
                return true;
            }
        }
        if (node == modifier) {
            setModifier((Modifier) replacementNode);
            return true;
        }
        for (int i = 0; i < subContracts.size(); i++) {
            if (subContracts.get(i) == node) {
                subContracts.set(i, (JmlContract) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlContract clone() {
        return (JmlContract) accept(new CloneVisitor(), null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlContract(TokenRange tokenRange, Behavior behavior, Modifier modifier, NodeList<JmlClause> clauses, NodeList<JmlContract> subContracts) {
        super(tokenRange);
        setBehavior(behavior);
        setModifier(modifier);
        setClauses(clauses);
        setSubContracts(subContracts);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlContractMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlContractMetaModel;
    }
}
