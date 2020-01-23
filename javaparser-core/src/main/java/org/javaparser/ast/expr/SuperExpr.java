/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package org.javaparser.ast.expr;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.OptionalProperty;
import org.javaparser.metamodel.SuperExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import java.util.function.Consumer;
import org.javaparser.ast.Generated;

/**
 * An occurrence of the "super" keyword. <br/>
 * <code>World.super.greet()</code> is a MethodCallExpr of method name greet,
 * and scope "World.super" which is a SuperExpr with typeName "World". <br/>
 * <code>super.name</code> is a FieldAccessExpr of field greet, and a SuperExpr as its scope.
 * This SuperExpr has no typeName.
 *
 * @author Julio Vilmar Gesser
 * @see org.javaparser.ast.stmt.ExplicitConstructorInvocationStmt
 * @see ThisExpr
 */
public class SuperExpr extends Expression {

    @OptionalProperty
    private Name typeName;

    public SuperExpr() {
        this(null, null);
    }

    @AllFieldsConstructor
    public SuperExpr(final Name typeName) {
        this(null, typeName);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public SuperExpr(TokenRange tokenRange, Name typeName) {
        super(tokenRange);
        setTypeName(typeName);
        customInitialization();
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Name> getTypeName() {
        return Optional.ofNullable(typeName);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public SuperExpr setTypeName(final Name typeName) {
        if (typeName == this.typeName) {
            return (SuperExpr) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE_NAME, this.typeName, typeName);
        if (this.typeName != null)
            this.typeName.setParentNode(null);
        this.typeName = typeName;
        setAsParentNodeOf(typeName);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (typeName != null) {
            if (node == typeName) {
                removeTypeName();
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public SuperExpr clone() {
        return (SuperExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public SuperExprMetaModel getMetaModel() {
        return JavaParserMetaModel.superExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isSuperExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public SuperExpr asSuperExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifSuperExpr(Consumer<SuperExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<SuperExpr> toSuperExpr() {
        return Optional.of(this);
    }

    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public SuperExpr removeClassName() {
        return setTypeName((Name) null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (typeName != null) {
            if (node == typeName) {
                setTypeName((Name) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public SuperExpr removeTypeName() {
        return setTypeName((Name) null);
    }
}
