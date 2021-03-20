package com.github.javaparser.ast.jml.locref;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.observer.ObservableProperty;

import static com.github.javaparser.utils.Utils.assertNotNull;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.LocationSetFieldAccessMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.ast.Generated;

/**
 * @author Alexander Weigl
 * @version 1 (3/19/21)
 */
public class LocationSetFieldAccess extends LocationSetExpression {

    private LocationSetExpression scope;

    private SimpleName name;

    public LocationSetFieldAccess() {
    }

    @AllFieldsConstructor
    public LocationSetFieldAccess(LocationSetExpression scope, SimpleName name) {
        this.scope = scope;
        this.name = name;
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public LocationSetFieldAccess(TokenRange tokenRange, LocationSetExpression scope, SimpleName name) {
        super(tokenRange);
        setScope(scope);
        setName(name);
        customInitialization();
    }

    public static LocationSetExpression fromQualifiedName(LocationSetExpression prefix, Name name) {
        LocationSetExpression cur = prefix;
        //TODO weigl
        return cur;
    }

    public static LocationSetExpression forAllFields(TokenRange range, LocationSetExpression prefix) {
        return new LocationSetFieldAccess(range, prefix, new SimpleName("*"));
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
    public SimpleName getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetFieldAccess setName(final SimpleName name) {
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetExpression getScope() {
        return scope;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public LocationSetFieldAccess setScope(final LocationSetExpression scope) {
        assertNotNull(scope);
        if (scope == this.scope) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.SCOPE, this.scope, scope);
        if (this.scope != null)
            this.scope.setParentNode(null);
        this.scope = scope;
        setAsParentNodeOf(scope);
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
        if (node == name) {
            setName((SimpleName) replacementNode);
            return true;
        }
        if (node == scope) {
            setScope((LocationSetExpression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public LocationSetFieldAccess clone() {
        return (LocationSetFieldAccess) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public LocationSetFieldAccessMetaModel getMetaModel() {
        return JavaParserMetaModel.locationSetFieldAccessMetaModel;
    }
}
