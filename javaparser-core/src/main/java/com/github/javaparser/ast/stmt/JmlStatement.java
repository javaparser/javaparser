package com.github.javaparser.ast.stmt;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;

import java.util.Optional;
import java.util.function.Consumer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlStatementMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (3/18/21)
 */
public abstract class JmlStatement extends Statement {

    @AllFieldsConstructor
    public JmlStatement() {
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlStatement(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Override
    public boolean isJmlStatement() {
        return true;
    }

    @Override
    public JmlStatement asJmlStatement() {
        return this;
    }

    @Override
    public Optional<JmlStatement> toJmlStatement() {
        return Optional.of(this);
    }

    public void ifJmlStatement(Consumer<JmlStatement> action) {
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
    public JmlStatement clone() {
        return (JmlStatement) accept(new CloneVisitor(), null);
    }

    @Override
    public JmlStatementMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlStatementMetaModel;
    }
}
