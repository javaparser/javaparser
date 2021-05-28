package com.github.javaparser.ast.jml.locref;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.Expression;
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
import com.github.javaparser.metamodel.OptionalProperty;

import java.util.Optional;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (3/19/21)
 */
public class LocationSetArrayAccess extends LocationSetExpression {

    private static final Expression ALL_INDICES = new StringLiteralExpr("*");

    private Expression name;

    private Expression start;

    @OptionalProperty
    private Expression stop;

    public LocationSetArrayAccess() {
        this(null, null, null, null);
    }

    public LocationSetArrayAccess(Expression name, Expression start) {
        this(null, name, start, start);
    }

    @AllFieldsConstructor
    public LocationSetArrayAccess(Expression name, Expression start, Expression stop) {
        this(null, name, start, stop);
    }

    public LocationSetArrayAccess(TokenRange range, Expression prefix, Expression expr) {
        this(range, prefix, expr, expr);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LocationSetArrayAccess(TokenRange tokenRange, Expression name, Expression start, Expression stop) {
        super(tokenRange);
        setName(name);
        setStart(start);
        setStop(stop);
        customInitialization();
    }

    public static LocationSetExpression forAllIndices(TokenRange range, Expression prefix) {
        return new LocationSetArrayAccess(range, prefix, ALL_INDICES, ALL_INDICES);
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
    public Expression getStart() {
        return start;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetArrayAccess setStart(final Expression start) {
        assertNotNull(start);
        if (start == this.start) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.START, this.start, start);
        if (this.start != null)
            this.start.setParentNode(null);
        this.start = start;
        setAsParentNodeOf(start);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetArrayAccess setName(final Expression name) {
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
        if (stop != null) {
            if (node == stop) {
                removeStop();
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
        if (node == name) {
            setName((Expression) replacementNode);
            return true;
        }
        if (node == start) {
            setStart((Expression) replacementNode);
            return true;
        }
        if (stop != null) {
            if (node == stop) {
                setStop((Expression) replacementNode);
                return true;
            }
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

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isLocationSetArrayAccess() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public LocationSetArrayAccess asLocationSetArrayAccess() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<LocationSetArrayAccess> toLocationSetArrayAccess() {
        return Optional.of(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifLocationSetArrayAccess(Consumer<LocationSetArrayAccess> action) {
        action.accept(this);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getStop() {
        return Optional.ofNullable(stop);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetArrayAccess setStop(final Expression stop) {
        if (stop == this.stop) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.STOP, this.stop, stop);
        if (this.stop != null)
            this.stop.setParentNode(null);
        this.stop = stop;
        setAsParentNodeOf(stop);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public LocationSetArrayAccess removeStop() {
        return setStop(null);
    }
}
