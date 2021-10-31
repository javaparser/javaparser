package com.github.javaparser.ast.key.sv;

import com.github.javaparser.TokenRange;
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
import com.github.javaparser.metamodel.KeyExpressionSVMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyExpressionSV extends Expression {

    private String text;

    @AllFieldsConstructor
    public KeyExpressionSV(String text) {
        this.text = text;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyExpressionSV(TokenRange tokenRange, String text) {
        super(tokenRange);
        setText(text);
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
    public boolean isKeyExpressionSV() {
        return true;
    }

    @Override
    public KeyExpressionSV asKeyExpressionSV() {
        return this;
    }

    @Override
    public Optional<KeyExpressionSV> toKeyExpressionSV() {
        return Optional.of(this);
    }

    public void ifKeyExpressionSV(Consumer<KeyExpressionSV> action) {
        action.accept(this);
    }

    public String getText() {
        return text;
    }

    public KeyExpressionSV setText(final String text) {
        assertNotNull(text);
        if (text == this.text) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TEXT, this.text, text);
        this.text = text;
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
        return super.replace(node, replacementNode);
    }

    @Override
    public KeyExpressionSV clone() {
        return (KeyExpressionSV) accept(new CloneVisitor(), null);
    }

    @Override
    public KeyExpressionSVMetaModel getMetaModel() {
        return JavaParserMetaModel.keyExpressionSVMetaModel;
    }
}
