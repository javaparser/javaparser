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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.ArrayAccessExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;

import javax.annotation.Generated;
import java.util.Optional;
import java.util.function.Consumer;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Array brackets [] being used to get a value from an array.
 * In <br/><code>getNames()[15*15]</code> the name expression is getNames() and the index expression is 15*15.
 *
 * @author Julio Vilmar Gesser
 */
public final class ArrayAccessExpr extends Expression {

    private Expression name;

    private Expression index;

    public ArrayAccessExpr() {
        this(null, new NameExpr(), new IntegerLiteralExpr());
    }

    @AllFieldsConstructor
    public ArrayAccessExpr(Expression name, Expression index) {
        this(null, name, index);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ArrayAccessExpr(TokenRange tokenRange, Expression name, Expression index) {
        super(tokenRange);
        setName(name);
        setIndex(index);
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
    public Expression getIndex() {
        return index;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Expression getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ArrayAccessExpr setIndex(final Expression index) {
        assertNotNull(index);
        if (index == this.index) {
            return (ArrayAccessExpr) this;
        }
        notifyPropertyChange(ObservableProperty.INDEX, this.index, index);
        if (this.index != null)
            this.index.setParentNode(null);
        this.index = index;
        setAsParentNodeOf(index);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ArrayAccessExpr setName(final Expression name) {
        assertNotNull(name);
        if (name == this.name) {
            return (ArrayAccessExpr) this;
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
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ArrayAccessExpr clone() {
        return (ArrayAccessExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ArrayAccessExprMetaModel getMetaModel() {
        return JavaParserMetaModel.arrayAccessExprMetaModel;
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
            setName((Expression) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isArrayAccessExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ArrayAccessExpr asArrayAccessExpr() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifArrayAccessExpr(Consumer<ArrayAccessExpr> action) {
        action.accept(this);
    }

    /**
     * Convenience method to resolve the declaration corresponding to the accessed array. If successful, an
     * {@code Optional} of a {@link ResolvedValueDeclaration} representing the declaration of the array accessed by this
     * {@code ArrayAccessExpr} is returned.
     * <p>
     * Note that the accessed array must not necessarily have an explicit definition anywhere in the source code. For
     * instance, it could instead access an array dynamically like: {@code (new String[] {"One", "Two", "Three"})[2]},
     * or it could access the return value of a method like: {@code foo()[2]}.
     * <p>
     * If, however, the accessed array is a name (e.g., {@code foo[2]}) or a field access expression (e.g.,
     * {@code this.foo[2]}), then the accessed array must correspond to a declaration of a local variable or a field,
     * and this method will attempt to resolve that variable or field.
     * <p>
     * In addition, an array access of an enclosed expression may or may not refer to a declaration: For instance,
     * {@code (foo)[2]} does, but {@code (foo())[2]} does not.
     * <p>
     * When this array access's name is a {@link NameExpr} or {@link FieldAccessExpr}, then this method will attempt to
     * resolve the corresponding declaration. If this arrray access's name is an {@link EnclosedExpr}, that expression's
     * inner expression is used (multiple nested enclosed expressions are also handled). If this array access's name is
     * not a {@link NameExpr} nor a {@link FieldAccessExpr} nor an {@link EnclosedExpr} which wraps one of the latter
     * two expressions, then an empty Optional is returned.
     *
     * @return an Optional of {@link ResolvedValueDeclaration} representing the declaration of the accessed array if
     * this array access's name is a {@link NameExpr} or  {@link FieldAccessExpr} or an {@link EnclosedExpr} which wraps
     * one of the latter two expressions; and an empty Optional otherwise.
     * @throws UnsolvedSymbolException if this array access's name is a {@link NameExpr} or  {@link FieldAccessExpr} or
     * an {@link EnclosedExpr} which wraps one of the latter two expressions, yet the corresponding declaration could
     * not be resolved.
     */
    public Optional<ResolvedValueDeclaration> resolveAccessedArray() {
        Expression name = getName();
        while (name instanceof EnclosedExpr) {
            name = ((EnclosedExpr) name).getInner();
        }
        // the array access can only refer to an array definition (instead of an array returned from somewhere, for
        // example) if the accessed name is a field access expression or a name expression.
        if (name instanceof NameExpr || name instanceof FieldAccessExpr) {
            return Optional.of(getSymbolResolver().resolveDeclaration(name, ResolvedValueDeclaration.class));
        }

        return Optional.empty();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ArrayAccessExpr> toArrayAccessExpr() {
        return Optional.of(this);
    }
}
