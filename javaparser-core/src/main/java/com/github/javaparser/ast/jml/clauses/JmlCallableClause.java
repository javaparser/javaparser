package com.github.javaparser.ast.jml.clauses;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlCallableClauseMetaModel;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;
import org.jspecify.annotations.NonNull;

/**
 * @author Alexander Weigl
 * @version 1 (2/22/21)
 */
public class JmlCallableClause extends JmlClause {

    private NodeList<JmlMethodSignature> methodSignatures = new NodeList<JmlMethodSignature>();

    @AllFieldsConstructor
    public JmlCallableClause(SimpleName name, NodeList<JmlMethodSignature> methodSignatures) {
        super(name);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlCallableClause(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlCallableClause clone() {
        return (JmlCallableClause) accept(new CloneVisitor(), null);
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
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlCallableClauseMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlCallableClauseMetaModel;
    }

    @Override
    public JmlClauseKind getKind() {
        return JmlClauseKind.CALLABLE;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlCallableClause() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlCallableClause asJmlCallableClause() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlCallableClause> toJmlCallableClause() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlCallableClause(Consumer<JmlCallableClause> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlMethodSignature> getMethodSignatures() {
        return methodSignatures;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlCallableClause setMethodSignatures(final NodeList<JmlMethodSignature> methodSignatures) {
        assertNotNull(methodSignatures);
        if (methodSignatures == this.methodSignatures) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.METHOD_SIGNATURES, this.methodSignatures, methodSignatures);
        if (this.methodSignatures != null) this.methodSignatures.setParentNode(null);
        this.methodSignatures = methodSignatures;
        setAsParentNodeOf(methodSignatures);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < methodSignatures.size(); i++) {
            if (methodSignatures.get(i) == node) {
                methodSignatures.remove(i);
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
        for (int i = 0; i < methodSignatures.size(); i++) {
            if (methodSignatures.get(i) == node) {
                methodSignatures.set(i, (JmlMethodSignature) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlCallableClause(TokenRange tokenRange, SimpleName name, NodeList<JmlMethodSignature> methodSignatures) {
        super(tokenRange, name);
        setMethodSignatures(methodSignatures);
        customInitialization();
    }

    @NonNull()
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<JmlMethodSignature> methodSignatures() {
        return Objects.requireNonNull(methodSignatures);
    }
}
