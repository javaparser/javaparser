package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.JavaToken;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlBinaryInfixExprMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (7/3/21)
 */
public class JmlBinaryInfixExpr extends Expression {

    private Expression left;

    private Expression right;

    private SimpleName operator;

    public JmlBinaryInfixExpr(Expression left, Expression right, JavaToken operator) {
        this(null, left, right, nameFromToken(operator));
    }

    @AllFieldsConstructor
    public JmlBinaryInfixExpr(Expression left, Expression right, SimpleName operator) {
        this(null, left, right, operator);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlBinaryInfixExpr(TokenRange tokenRange, Expression left, Expression right, SimpleName operator) {
        super(tokenRange);
        setLeft(left);
        setRight(right);
        setOperator(operator);
        customInitialization();
    }

    public JmlBinaryInfixExpr(TokenRange range, Expression left, Expression right, JavaToken op) {
        this(range, left, right, nameFromToken(op));
    }

    private static SimpleName nameFromToken(JavaToken op) {
        return new SimpleName(new TokenRange(op, op), op.getText());
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
    public boolean isJmlBinaryInfixExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlBinaryInfixExpr asJmlBinaryInfixExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlBinaryInfixExpr> toJmlBinaryInfixExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlBinaryInfixExpr(Consumer<JmlBinaryInfixExpr> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getLeft() {
        return left;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlBinaryInfixExpr setLeft(final Expression left) {
        assertNotNull(left);
        if (left == this.left) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.LEFT, this.left, left);
        if (this.left != null)
            this.left.setParentNode(null);
        this.left = left;
        setAsParentNodeOf(left);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getOperator() {
        return operator;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlBinaryInfixExpr setOperator(final SimpleName operator) {
        assertNotNull(operator);
        if (operator == this.operator) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.OPERATOR, this.operator, operator);
        if (this.operator != null)
            this.operator.setParentNode(null);
        this.operator = operator;
        setAsParentNodeOf(operator);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getRight() {
        return right;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlBinaryInfixExpr setRight(final Expression right) {
        assertNotNull(right);
        if (right == this.right) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.RIGHT, this.right, right);
        if (this.right != null)
            this.right.setParentNode(null);
        this.right = right;
        setAsParentNodeOf(right);
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
        if (node == left) {
            setLeft((Expression) replacementNode);
            return true;
        }
        if (node == operator) {
            setOperator((SimpleName) replacementNode);
            return true;
        }
        if (node == right) {
            setRight((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlBinaryInfixExpr clone() {
        return (JmlBinaryInfixExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlBinaryInfixExprMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlBinaryInfixExprMetaModel;
    }
}
