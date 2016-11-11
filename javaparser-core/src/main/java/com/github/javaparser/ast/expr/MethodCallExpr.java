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

import static com.github.javaparser.utils.Utils.assertNotNull;

import java.util.Optional;

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class MethodCallExpr extends Expression implements 
        NodeWithTypeArguments<MethodCallExpr>,
        NodeWithArguments<MethodCallExpr>,
        NodeWithSimpleName<MethodCallExpr> {

    private Expression scope;

    private NodeList<Type<?>> typeArguments;

    private SimpleName name;

    private NodeList<Expression> args;

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

    public MethodCallExpr(final Expression scope, final SimpleName name, final NodeList<Expression> args) {
        this(null,
                scope,
                new NodeList<>(),
                name,
                args);
    }

	public MethodCallExpr(final Range range, final Expression scope, final NodeList<Type<?>> typeArguments, final SimpleName name, final NodeList<Expression> args) {
		super(range);
		setScope(scope);
		setTypeArguments(typeArguments);
		setName(name);
		setArgs(args);
	}

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public NodeList<Expression> getArgs() {
        return args;
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    public Expression getScope() {
        return scope;
    }

    @Override
	public MethodCallExpr setArgs(final NodeList<Expression> args) {
		this.args = assertNotNull(args);
		setAsParentNodeOf(this.args);
        return this;
	}

    @Override
    public MethodCallExpr setName(final SimpleName name) {
        this.name = name;
        setAsParentNodeOf(this.name);
        return this;
    }

    public MethodCallExpr setScope(final Expression scope) {
        this.scope = scope;
        setAsParentNodeOf(this.scope);
        return this;
    }

    @Override
    public Optional<NodeList<Type<?>>> getTypeArguments() {
        return Optional.ofNullable(typeArguments);
    }

    /**
     * Sets the typeArguments
     * 
     * @param typeArguments the typeArguments, can be null
     * @return this, the MethodCallExpr
     */
    @Override
    public MethodCallExpr setTypeArguments(final NodeList<Type<?>> types) {
        this.typeArguments = types;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
