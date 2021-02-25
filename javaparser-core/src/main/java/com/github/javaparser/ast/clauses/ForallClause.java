package com.github.javaparser.ast.clauses;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ForallClauseMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/22/21)
 */
public class ForallClause extends Clause {

    private NodeList<JmlBoundVariable> variables;

    @AllFieldsConstructor
    public ForallClause(NodeList<JmlBoundVariable> variables) {
        this(null, variables);
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
    public NodeList<JmlBoundVariable> getVariables() {
        return variables;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ForallClause setVariables(final NodeList<JmlBoundVariable> variables) {
        assertNotNull(variables);
        if (variables == this.variables) {
            return (ForallClause) this;
        }
        notifyPropertyChange(ObservableProperty.VARIABLES, this.variables, variables);
        if (this.variables != null)
            this.variables.setParentNode(null);
        this.variables = variables;
        setAsParentNodeOf(variables);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < variables.size(); i++) {
            if (variables.get(i) == node) {
                variables.remove(i);
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
        for (int i = 0; i < variables.size(); i++) {
            if (variables.get(i) == node) {
                variables.set(i, (JmlBoundVariable) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ForallClause clone() {
        return (ForallClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ForallClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.forallClauseMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ForallClause(TokenRange tokenRange, NodeList<JmlBoundVariable> variables) {
        super(tokenRange);
        setVariables(variables);
        customInitialization();
    }
}
