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
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A method call on an object. <br/><code>circle.circumference()</code> <br/>In <code>a.&lt;String&gt;bb(15);</code> a
 * is the scope, String is a type argument, bb is the name and 15 is an argument.
 *
 * @author Julio Vilmar Gesser
 */
public final class MethodCallExpr extends Expression implements
        NodeWithTypeArguments<MethodCallExpr>,
        NodeWithArguments<MethodCallExpr>,
        NodeWithSimpleName<MethodCallExpr> {

    private Expression scope;

    private NodeList<Type> typeArguments;

    private SimpleName name;

    private NodeList<Expression> arguments;

    public MethodCallExpr() {
        this(null,
                null,
                new NodeList<>(),
                new SimpleName(),
                new NodeList<>());
    }

    public MethodCallExpr(final Expression scope, final String name) {
        this(null,
                scope,
                new NodeList<>(),
                new SimpleName(name),
                new NodeList<>());
    }

    public MethodCallExpr(final Expression scope, final SimpleName name, final NodeList<Expression> arguments) {
        this(null,
                scope,
                new NodeList<>(),
                name,
                arguments);
    }

    public MethodCallExpr(final Range range, final Expression scope, final NodeList<Type> typeArguments, final SimpleName name, final NodeList<Expression> arguments) {
        super(range);
        setScope(scope);
        setTypeArguments(typeArguments);
        setName(name);
        setArguments(arguments);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public NodeList<Expression> getArguments() {
        return arguments;
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    public Optional<Expression> getScope() {
        return Optional.ofNullable(scope);
    }

    public MethodCallExpr setArguments(final NodeList<Expression> arguments) {
        notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        this.arguments = assertNotNull(arguments);
        setAsParentNodeOf(this.arguments);
        return this;
    }

    @Override
    public MethodCallExpr setName(final SimpleName name) {
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        this.name = name;
        setAsParentNodeOf(this.name);
        return this;
    }

    public MethodCallExpr setScope(final Expression scope) {
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
     * Sets the typeArguments
     *
     * @param typeArguments the typeArguments, can be null
     * @return this, the MethodCallExpr
     */
    @Override
    public MethodCallExpr setTypeArguments(final NodeList<Type> typeArguments) {
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        this.typeArguments = typeArguments;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
