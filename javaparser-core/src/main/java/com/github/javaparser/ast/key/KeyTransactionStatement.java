package com.github.javaparser.ast.key;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyTransactionStatementMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyTransactionStatement extends Statement {

    private TransactionType type;

    @AllFieldsConstructor
    public KeyTransactionStatement(TransactionType type) {
        this.type = type;
    }

    public KeyTransactionStatement(TokenRange range, JavaToken begin) {
        super(range);
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

    public enum TransactionType {
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isKeyTransactionStatement() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyTransactionStatement asKeyTransactionStatement() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyTransactionStatement> toKeyTransactionStatement() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyTransactionStatement(Consumer<KeyTransactionStatement> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public TransactionType getType() {
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyTransactionStatement setType(final TransactionType type) {
        assertNotNull(type);
        if (type == this.type) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyTransactionStatement clone() {
        return (KeyTransactionStatement) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyTransactionStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.keyTransactionStatementMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyTransactionStatement(TokenRange tokenRange, TransactionType type) {
        super(tokenRange);
        setType(type);
        customInitialization();
    }
}
