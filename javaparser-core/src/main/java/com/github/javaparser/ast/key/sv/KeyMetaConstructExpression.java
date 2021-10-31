package com.github.javaparser.ast.key.sv;

import com.github.javaparser.JavaToken;
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
import com.github.javaparser.metamodel.KeyMetaConstructExpressionMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyMetaConstructExpression extends Expression {

    private String text;

    private Expression child;

    @AllFieldsConstructor
    public KeyMetaConstructExpression(String text, Expression child) {
        this.text = text;
        this.child = child;
    }

    public KeyMetaConstructExpression(TokenRange tokenRange, JavaToken kind, Expression child) {
        this(tokenRange, kind.getText(), child);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyMetaConstructExpression(TokenRange tokenRange, String text, Expression child) {
        super(tokenRange);
        setText(text);
        setChild(child);
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isKeyMetaConstructExpression() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public KeyMetaConstructExpression asKeyMetaConstructExpression() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<KeyMetaConstructExpression> toKeyMetaConstructExpression() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifKeyMetaConstructExpression(Consumer<KeyMetaConstructExpression> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getChild() {
        return child;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMetaConstructExpression setChild(final Expression child) {
        assertNotNull(child);
        if (child == this.child) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.CHILD, this.child, child);
        if (this.child != null)
            this.child.setParentNode(null);
        this.child = child;
        setAsParentNodeOf(child);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public String getText() {
        return text;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public KeyMetaConstructExpression setText(final String text) {
        assertNotNull(text);
        if (text == this.text) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.TEXT, this.text, text);
        this.text = text;
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
        if (node == child) {
            setChild((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public KeyMetaConstructExpression clone() {
        return (KeyMetaConstructExpression) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public KeyMetaConstructExpressionMetaModel getMetaModel() {
        return JavaParserMetaModel.keyMetaConstructExpressionMetaModel;
    }
}
