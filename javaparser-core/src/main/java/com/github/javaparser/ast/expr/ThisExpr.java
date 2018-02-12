/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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
package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.metamodel.ThisExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedTypeDeclaration;
import java.util.function.Consumer;

/**
 * An occurrence of the "this" keyword. <br/><code>World.this.greet()</code> is a MethodCallExpr of method name greet,
 * and scope "World.super" which is a ThisExpr with classExpr "World". <br/><code>this.name</code> is a
 * FieldAccessExpr of field greet, and a ThisExpr as its scope. The ThisExpr has no classExpr.
 *
 * @author Julio Vilmar Gesser
 * @see com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt
 * @see ThisExpr
 */
public final class ThisExpr extends Expression implements Resolvable<ResolvedTypeDeclaration> {

    @OptionalProperty
    private Expression classExpr;

    public ThisExpr() {
        this(null, null);
    }

    @AllFieldsConstructor
    public ThisExpr(final Expression classExpr) {
        this(null, classExpr);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ThisExpr(TokenRange tokenRange, Expression classExpr) {
        super(tokenRange);
        setClassExpr(classExpr);
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
    public Optional<Expression> getClassExpr() {
        return Optional.ofNullable(classExpr);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ThisExpr setClassExpr(final Expression classExpr) {
        if (classExpr == this.classExpr) {
            return (ThisExpr) this;
        }
        notifyPropertyChange(ObservableProperty.CLASS_EXPR, this.classExpr, classExpr);
        if (this.classExpr != null)
            this.classExpr.setParentNode(null);
        this.classExpr = classExpr;
        setAsParentNodeOf(classExpr);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (classExpr != null) {
            if (node == classExpr) {
                removeClassExpr();
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public ThisExpr removeClassExpr() {
        return setClassExpr((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ThisExpr clone() {
        return (ThisExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ThisExprMetaModel getMetaModel() {
        return JavaParserMetaModel.thisExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (classExpr != null) {
            if (node == classExpr) {
                setClassExpr((Expression) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isThisExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ThisExpr asThisExpr() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifThisExpr(Consumer<ThisExpr> action) {
        action.accept(this);
    }

    @Override
    public ResolvedTypeDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedTypeDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ThisExpr> toThisExpr() {
        return Optional.of(this);
    }
}
