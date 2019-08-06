package com.github.javaparser.ast.stmt;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithExpression;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;
import java.util.function.Consumer;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.YieldStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <h1>The yield statement</h1>
 * <h2>Java 1.0-11</h2>
 * Does not exist.
 * <h2>Java 12</h2>
 * Yields an expression to be used in the switch-expression:
 * <br/><code>yield 123+456;</code>
 * <br/><code>yield "more or less";</code>
 */
public class YieldStmt extends Statement implements NodeWithExpression {

    private Expression expression;

    public YieldStmt() {
        this(null, new NameExpr());
    }

    @AllFieldsConstructor
    public YieldStmt(final Expression expression) {
        this(null, expression);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public YieldStmt(TokenRange tokenRange, Expression expression) {
        super(tokenRange);
        setExpression(expression);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getExpression() {
        return expression;
    }

    /**
     * Sets the label
     *
     * @param expression the label or the expression, can be null
     * @return this, the YieldStmt
     */
    @Override
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public YieldStmt setExpression(final Expression expression) {
        assertNotNull(expression);
        if (expression == this.expression) {
            return (YieldStmt) this;
        }
        notifyPropertyChange(ObservableProperty.VALUE, this.expression, expression);
        if (this.expression != null)
            this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
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
    public boolean isYieldStmt() {
        return true;
    }

    @Override
    public YieldStmt asYieldStmt() {
        return this;
    }

    @Override
    public Optional<YieldStmt> toYieldStmt() {
        return Optional.of(this);
    }

    public void ifYieldStmt(Consumer<YieldStmt> action) {
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
        if (node == expression) {
            setExpression((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public YieldStmt clone() {
        return (YieldStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public YieldStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.yieldStmtMetaModel;
    }
}
