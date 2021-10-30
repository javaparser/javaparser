package com.github.javaparser.ast.key;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.KeyMergePointStatementMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyMergePointStatement extends Statement {

    @AllFieldsConstructor
    public KeyMergePointStatement() {
        this(null);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyMergePointStatement(TokenRange tokenRange) {
        super(tokenRange);
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

    @Override
    public boolean isKeyMergePointStatement() {
        return true;
    }

    @Override
    public KeyMergePointStatement asKeyMergePointStatement() {
        return this;
    }

    @Override
    public Optional<KeyMergePointStatement> toKeyMergePointStatement() {
        return Optional.of(this);
    }

    public void ifKeyMergePointStatement(Consumer<KeyMergePointStatement> action) {
        action.accept(this);
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
        return super.replace(node, replacementNode);
    }

    @Override
    public KeyMergePointStatement clone() {
        return (KeyMergePointStatement) accept(new CloneVisitor(), null);
    }

    @Override
    public KeyMergePointStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.keyMergePointStatementMetaModel;
    }
}
