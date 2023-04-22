/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.EnclosedExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * An expression between ( ).
 * <br>{@code (1+1)}
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
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public EnclosedExpr(TokenRange tokenRange, Expression inner) {
        super(tokenRange);
        setInner(inner);
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
    public Expression getInner() {
        return inner;
    }

    /**
     * Sets the inner expression
     *
     * @param inner the inner expression, can be null
     * @return this, the EnclosedExpr
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public EnclosedExpr setInner(final Expression inner) {
        assertNotNull(inner);
        if (inner == this.inner) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.INNER, this.inner, inner);
        if (this.inner != null)
            this.inner.setParentNode(null);
        this.inner = inner;
        setAsParentNodeOf(inner);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public EnclosedExpr clone() {
        return (EnclosedExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public EnclosedExprMetaModel getMetaModel() {
        return JavaParserMetaModel.enclosedExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (node == inner) {
            setInner((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnclosedExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EnclosedExpr asEnclosedExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnclosedExpr(Consumer<EnclosedExpr> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnclosedExpr> toEnclosedExpr() {
        return Optional.of(this);
    }

    /*
     * On Parenthesized Expressions, if the contained expression is a poly expression (§15.2), the parenthesized expression is also a poly expression. Otherwise, it is a standalone expression.
     * (https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.8.5)
     */
    @Override
    public boolean isPolyExpression() {
        return getInner().isPolyExpression();
    }
}
