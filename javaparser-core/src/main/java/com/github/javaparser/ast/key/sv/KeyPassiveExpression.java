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
import com.github.javaparser.metamodel.KeyPassiveExpressionMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

public class KeyPassiveExpression extends Expression {

    private Expression expr;

    @AllFieldsConstructor
    public KeyPassiveExpression(Expression expr) {
        this.expr = expr;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public KeyPassiveExpression(TokenRange tokenRange, Expression expr) {
        super(tokenRange);
        setExpr(expr);
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
    public boolean isKeyPassiveExpression() {
        return true;
    }

    @Override
    public KeyPassiveExpression asKeyPassiveExpression() {
        return this;
    }

    @Override
    public Optional<KeyPassiveExpression> toKeyPassiveExpression() {
        return Optional.of(this);
    }

    public void ifKeyPassiveExpression(Consumer<KeyPassiveExpression> action) {
        action.accept(this);
    }

    public Expression getExpr() {
        return expr;
    }

    public KeyPassiveExpression setExpr(final Expression expr) {
        assertNotNull(expr);
        if (expr == this.expr) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPR, this.expr, expr);
        if (this.expr != null)
            this.expr.setParentNode(null);
        this.expr = expr;
        setAsParentNodeOf(expr);
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
        if (node == expr) {
            setExpr((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public KeyPassiveExpression clone() {
        return (KeyPassiveExpression) accept(new CloneVisitor(), null);
    }

    @Override
    public KeyPassiveExpressionMetaModel getMetaModel() {
        return JavaParserMetaModel.keyPassiveExpressionMetaModel;
    }
}
