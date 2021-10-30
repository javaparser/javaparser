package com.github.javaparser.ast.key;

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
import com.github.javaparser.metamodel.KeyRangeExpressionMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyRangeExpression extends Expression {

    private Expression lower;

    private Expression upper;

    @AllFieldsConstructor
    public KeyRangeExpression(Expression start, Expression upper) {
        this(null, start, upper);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyRangeExpression(TokenRange tokenRange, Expression start, Expression upper) {
        super(tokenRange);
        setLower(start);
        setUpper(upper);
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
    public boolean isKeyRangeExpression() {
        return true;
    }

    @Override
    public KeyRangeExpression asKeyRangeExpression() {
        return this;
    }

    @Override
    public Optional<KeyRangeExpression> toKeyRangeExpression() {
        return Optional.of(this);
    }

    public void ifKeyRangeExpression(Consumer<KeyRangeExpression> action) {
        action.accept(this);
    }

    public Expression getUpper() {
        return upper;
    }

    public KeyRangeExpression setUpper(final Expression upper) {
        assertNotNull(upper);
        if (upper == this.upper) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.END, this.upper, upper);
        if (this.upper != null)
            this.upper.setParentNode(null);
        this.upper = upper;
        setAsParentNodeOf(upper);
        return this;
    }

    public Expression getLower() {
        return lower;
    }

    public KeyRangeExpression setLower(final Expression lower) {
        assertNotNull(lower);
        if (lower == this.lower) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.START, this.lower, lower);
        if (this.lower != null)
            this.lower.setParentNode(null);
        this.lower = lower;
        setAsParentNodeOf(lower);
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
        if (node == upper) {
            setUpper((Expression) replacementNode);
            return true;
        }
        if (node == lower) {
            setLower((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public KeyRangeExpression clone() {
        return (KeyRangeExpression) accept(new CloneVisitor(), null);
    }

    @Override
    public KeyRangeExpressionMetaModel getMetaModel() {
        return JavaParserMetaModel.keyRangeExpressionMetaModel;
    }
}
