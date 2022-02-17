package com.github.javaparser.ast.jml.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Jmlish;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.JmlMultiCompareExprMetaModel;
import com.github.javaparser.metamodel.NonEmptyProperty;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

import com.github.javaparser.ast.observer.ObservableProperty;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.Node;

/**
 * @author Alexander Weigl
 * @version 1 (2/21/21)
 */
public class JmlMultiCompareExpr extends Expression implements Jmlish {

    @NonEmptyProperty
    private NodeList<Expression> exprs;

    private List<BinaryExpr.Operator> operators;

    @AllFieldsConstructor
    public JmlMultiCompareExpr() {
    }

    public JmlMultiCompareExpr(TokenRange range, NodeList<Expression> exprs, List<BinaryExpr.Operator> operators) {
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
    public boolean hasParentNode() {
        return false;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isJmlMultiCompareExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public JmlMultiCompareExpr asJmlMultiCompareExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<JmlMultiCompareExpr> toJmlMultiCompareExpr() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifJmlMultiCompareExpr(Consumer<JmlMultiCompareExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public JmlMultiCompareExpr clone() {
        return (JmlMultiCompareExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public JmlMultiCompareExprMetaModel getMetaModel() {
        return JavaParserMetaModel.jmlMultiCompareExprMetaModel;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public JmlMultiCompareExpr(TokenRange tokenRange) {
        super(tokenRange);
        customInitialization();
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getExprs() {
        return exprs;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public JmlMultiCompareExpr setExprs(final NodeList<Expression> exprs) {
        assertNotNull(exprs);
        if (exprs == this.exprs) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.EXPRS, this.exprs, exprs);
        if (this.exprs != null)
            this.exprs.setParentNode(null);
        this.exprs = exprs;
        setAsParentNodeOf(exprs);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Operator getOperators() {
        return operators;
    }

    public void setOperators(List<BinaryExpr.Operator> operators) {
        this.operators = operators;
    }

    public JmlMultiCompareExpr setOperators(final Operator operators) {
        assertNotNull(operators);
        if (operators == this.operators) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.OPERATORS, this.operators, operators);
        this.operators = operators;
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < exprs.size(); i++) {
            if (exprs.get(i) == node) {
                exprs.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < exprs.size(); i++) {
            if (exprs.get(i) == node) {
                exprs.set(i, (Expression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }
}
