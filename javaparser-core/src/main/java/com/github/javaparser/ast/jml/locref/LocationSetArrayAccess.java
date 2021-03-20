package com.github.javaparser.ast.jml.locref;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NullLiteralExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.LocationSetArrayAccessMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (3/19/21)
 */
public class LocationSetArrayAccess extends LocationSetExpression {

    private static final Expression ALL_INDICES = new StringLiteralExpr("*");

    private LocationSetExpression name;

    private Expression index;

    public LocationSetArrayAccess() {
        this(null, null, null);
    }

    @AllFieldsConstructor
    public LocationSetArrayAccess(LocationSetExpression name, Expression index) {
        this(null, name, index);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LocationSetArrayAccess(TokenRange tokenRange, LocationSetExpression name, Expression index) {
        super(tokenRange);
        setName(name);
        setIndex(index);
        customInitialization();
    }

    public static LocationSetExpression forAllIndices(TokenRange range, LocationSetExpression prefix) {
        return new LocationSetArrayAccess(range, prefix, ALL_INDICES);
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
    public Expression getIndex() {
        return index;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetArrayAccess setIndex(final Expression index) {
        assertNotNull(index);
        if (index == this.index) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.INDEX, this.index, index);
        if (this.index != null)
            this.index.setParentNode(null);
        this.index = index;
        setAsParentNodeOf(index);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetExpression getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetArrayAccess setName(final LocationSetExpression name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
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
        if (node == index) {
            setIndex((Expression) replacementNode);
            return true;
        }
        if (node == name) {
            setName((LocationSetExpression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public LocationSetArrayAccess clone() {
        return (LocationSetArrayAccess) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public LocationSetArrayAccessMetaModel getMetaModel() {
        return JavaParserMetaModel.locationSetArrayAccessMetaModel;
    }
}
