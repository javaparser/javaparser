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

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class FieldAccessExpr extends Expression implements NodeWithTypeArguments<FieldAccessExpr> {

    private Expression scope;

    private NodeList<Type> typeArguments;

    private SimpleName field;

    public FieldAccessExpr() {
        this(null, new ThisExpr(), new NodeList<>(), new SimpleName());
    }

    public FieldAccessExpr(final Expression scope, final String field) {
        this(null, scope, new NodeList<>(), new SimpleName(field));
    }

    public FieldAccessExpr(final Range range, final Expression scope, final NodeList<Type> typeArguments,
                           final SimpleName field) {
        super(range);
        setScope(scope);
        setTypeArguments(typeArguments);
        setFieldExpr(field);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public SimpleName getField() {
        return field;
    }

    public Optional<Expression> getScope() {
        return Optional.ofNullable(scope);
    }

    public FieldAccessExpr setField(final String field) {
        setFieldExpr(new SimpleName(field));
        return this;
    }

    public FieldAccessExpr setFieldExpr(SimpleName inner) {
        notifyPropertyChange(ObservableProperty.FIELD, this.field, inner);
        this.field = assertNotNull(inner);
        setAsParentNodeOf(this.field);
        return this;
    }

    /**
     * Sets the scope
     *
     * @param scope the scope, can be null
     * @return this, the FieldAccessExpr
     */
    public FieldAccessExpr setScope(final Expression scope) {
        notifyPropertyChange(ObservableProperty.SCOPE, this.scope, scope);
        this.scope = scope;
        setAsParentNodeOf(this.scope);
        return this;
    }

    @Override
    public Optional<NodeList<Type>> getTypeArguments() {
        return Optional.ofNullable(typeArguments);
    }

    /**
     * Sets the type arguments
     *
     * @param types the type arguments, can be null
     * @return this, the FieldAccessExpr
     */
    @Override
    public FieldAccessExpr setTypeArguments(final NodeList<Type> types) {
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        this.typeArguments = types;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
