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
import org.javaparser.metamodel.EnclosedExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import static org.javaparser.utils.Utils.assertNotNull;
import java.util.function.Consumer;
import org.javaparser.ast.Generated;

/**
 * An expression between ( ).
 * <br/><code>(1+1)</code>
 *
 * @author Julio Vilmar Gesser
 */
public class EnclosedExpr extends Expression {

    private Expression inner;

    public EnclosedExpr() {
        this(null, new StringLiteralExpr());
    }

    @AllFieldsConstructor
    public EnclosedExpr(final Expression inner) {
        this(null, inner);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public EnclosedExpr(TokenRange tokenRange, Expression inner) {
        super(tokenRange);
        setInner(inner);
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
    public Expression getInner() {
        return inner;
    }

    /**
     * Sets the inner expression
     *
     * @param inner the inner expression, can be null
     * @return this, the EnclosedExpr
     */
    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public EnclosedExpr setInner(final Expression inner) {
        assertNotNull(inner);
        if (inner == this.inner) {
            return (EnclosedExpr) this;
        }
        notifyPropertyChange(ObservableProperty.INNER, this.inner, inner);
        if (this.inner != null)
            this.inner.setParentNode(null);
        this.inner = inner;
        setAsParentNodeOf(inner);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public EnclosedExpr removeInner() {
        return setInner((Expression) null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public EnclosedExpr clone() {
        return (EnclosedExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public EnclosedExprMetaModel getMetaModel() {
        return JavaParserMetaModel.enclosedExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == inner) {
            setInner((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnclosedExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public EnclosedExpr asEnclosedExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnclosedExpr(Consumer<EnclosedExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnclosedExpr> toEnclosedExpr() {
        return Optional.of(this);
    }
}
