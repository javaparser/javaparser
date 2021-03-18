package com.github.javaparser.ast.body;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

import com.github.javaparser.ast.observer.ObservableProperty;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JmlBodyDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * @author Alexander Weigl
 * @version 1 (2/24/21)
 */
public class JmlBodyDeclaration extends BodyDeclaration<JmlBodyDeclaration> {

    private boolean singleLine;

    private Set<String> jmlTags;

    private NodeList<JmlClassLevel> elements;

    @AllFieldsConstructor
    public JmlBodyDeclaration(boolean singleLine, Set<String> jmlTags, NodeList<JmlClassLevel> elements) {
        this.singleLine = singleLine;
        this.jmlTags = jmlTags;
        this.elements = elements;
    }

    public JmlBodyDeclaration(TokenRange range, boolean singleLine, Set<String> jmlTags, NodeList<JmlClassLevel> elements) {
        super(range);
        this.singleLine = singleLine;
        this.jmlTags = jmlTags;
        this.elements = elements;
    }

    public JmlBodyDeclaration() {
        this(null);
    }

    public JmlBodyDeclaration(TokenRange range) {
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

    @Override
    public boolean isJmlBodyDeclaration() {
        return true;
    }

    @Override
    public JmlBodyDeclaration asJmlBodyDeclaration() {
        return this;
    }

    @Override
    public Optional<JmlBodyDeclaration> toJmlBodyDeclaration() {
        return Optional.of(this);
    }

    @Override
    public void ifJmlBodyDeclaration(Consumer<JmlBodyDeclaration> action) {
        action.accept(this);
    }

    public JmlClassLevel getWrapped() {
        return wrapped;
    }

    public JmlBodyDeclaration setWrapped(final JmlClassLevel wrapped) {
        assertNotNull(wrapped);
        if (wrapped == this.wrapped) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.WRAPPED, this.wrapped, wrapped);
        if (this.wrapped != null)
            this.wrapped.setParentNode(null);
        this.wrapped = wrapped;
        setAsParentNodeOf(wrapped);
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
        if (node == wrapped) {
            setWrapped((JmlClassLevel) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public JmlBodyDeclaration clone() {
        return (JmlBodyDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    public JmlBodyDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlBodyDeclarationMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    public JmlBodyDeclaration(TokenRange tokenRange, JmlClassLevel wrapped) {
        super(tokenRange);
        setWrapped(wrapped);
        customInitialization();
    }
}
