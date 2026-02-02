package com.github.javaparser.ast.jml.clauses;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlForallClauseMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/22/21)
 */
public class JmlForallClause extends JmlClause implements MethodContractable {

    private NodeList<Parameter> boundedVariables;

    @AllFieldsConstructor
    public JmlForallClause(NodeList<Parameter> boundedVariables) {
        this(null, boundedVariables);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlForallClause(TokenRange tokenRange, NodeList<Parameter> boundedVariables) {
        super(tokenRange);
        setBoundedVariables(boundedVariables);
        customInitialization();
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
    public NodeList<Parameter> getBoundedVariables() {
        return boundedVariables;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlForallClause setBoundedVariables(final NodeList<Parameter> boundedVariables) {
        assertNotNull(boundedVariables);
        if (boundedVariables == this.boundedVariables) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BOUNDED_VARIABLES, this.boundedVariables, boundedVariables);
        if (this.boundedVariables != null) this.boundedVariables.setParentNode(null);
        this.boundedVariables = boundedVariables;
        setAsParentNodeOf(boundedVariables);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < boundedVariables.size(); i++) {
            if (boundedVariables.get(i) == node) {
                boundedVariables.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < boundedVariables.size(); i++) {
            if (boundedVariables.get(i) == node) {
                boundedVariables.set(i, (Parameter) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlForallClause clone() {
        return (JmlForallClause) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlForallClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlForallClauseMetaModel;
    }

    @Override
    public JmlClauseKind getKind() {
        return JmlClauseKind.FORALL;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlForallClause() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlForallClause asJmlForallClause() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlForallClause> toJmlForallClause() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlForallClause(Consumer<JmlForallClause> action) {
        action.accept(this);
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Parameter> boundedVariables() {
        return Objects.requireNonNull(boundedVariables);
    }
}
