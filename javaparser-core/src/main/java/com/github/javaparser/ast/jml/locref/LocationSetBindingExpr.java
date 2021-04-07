package com.github.javaparser.ast.jml.locref;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.jml.JmlKeyword;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.ast.observer.ObservableProperty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import java.util.Optional;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.LocationSetBindingExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (3/19/21)
 */
public class LocationSetBindingExpr extends LocationSetExpression {

    public enum Quantifier implements JmlKeyword {

        INFINITE_UNION;

        private final String symbol = "\\" + name().toLowerCase();

        @Override
        public String jmlSymbol() {
            return symbol;
        }
    }

    private Quantifier quantifier;

    private VariableDeclarationExpr boundedVars;

    @OptionalProperty
    private Expression predicate;

    private LocationSetExpression expr;

    public LocationSetBindingExpr() {
        this(Quantifier.INFINITE_UNION, new NodeList<>(), null, null);
    }

    @AllFieldsConstructor
    public LocationSetBindingExpr(Quantifier quantifier, NodeList<VariableDeclarator> boundedVars, Expression predicate, LocationSetExpression expr) {
        this(null, Quantifier.INFINITE_UNION, null, predicate, expr);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LocationSetBindingExpr(TokenRange tokenRange, Quantifier quantifier, VariableDeclarationExpr boundedVars, Expression predicate, LocationSetExpression expr) {
        super(tokenRange);
        setQuantifier(quantifier);
        setBoundedVars(boundedVars);
        setPredicate(predicate);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public VariableDeclarationExpr getBoundedVars() {
        return boundedVars;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetBindingExpr setBoundedVars(final VariableDeclarationExpr boundedVars) {
        assertNotNull(boundedVars);
        if (boundedVars == this.boundedVars) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.BOUNDED_VARS, this.boundedVars, boundedVars);
        if (this.boundedVars != null)
            this.boundedVars.setParentNode(null);
        this.boundedVars = boundedVars;
        setAsParentNodeOf(boundedVars);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetExpression getExpr() {
        return expr;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetBindingExpr setExpr(final LocationSetExpression expr) {
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getPredicate() {
        return Optional.ofNullable(predicate);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetBindingExpr setPredicate(final Expression predicate) {
        if (predicate == this.predicate) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.PREDICATE, this.predicate, predicate);
        if (this.predicate != null)
            this.predicate.setParentNode(null);
        this.predicate = predicate;
        setAsParentNodeOf(predicate);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Quantifier getQuantifier() {
        return quantifier;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetBindingExpr setQuantifier(final Quantifier quantifier) {
        assertNotNull(quantifier);
        if (quantifier == this.quantifier) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.QUANTIFIER, this.quantifier, quantifier);
        this.quantifier = quantifier;
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public LocationSetBindingExpr removePredicate() {
        return setPredicate((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (predicate != null) {
            if (node == predicate) {
                removePredicate();
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == boundedVars) {
            setBoundedVars((VariableDeclarationExpr) replacementNode);
            return true;
        }
        if (node == expr) {
            setExpr((LocationSetExpression) replacementNode);
            return true;
        }
        if (predicate != null) {
            if (node == predicate) {
                setPredicate((Expression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public LocationSetBindingExpr clone() {
        return (LocationSetBindingExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public LocationSetBindingExprMetaModel getMetaModel() {
        return JavaParserMetaModel.locationSetBindingExprMetaModel;
    }
}
