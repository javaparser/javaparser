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

    public NodeList<Expression> getExprs() {
        return exprs;
    }

    public void setExprs(NodeList<Expression> exprs) {
        this.exprs = exprs;
    }

    public List<BinaryExpr.Operator> getOperators() {
        return operators;
    }

    public void setOperators(List<BinaryExpr.Operator> operators) {
        this.operators = operators;
    }
}
