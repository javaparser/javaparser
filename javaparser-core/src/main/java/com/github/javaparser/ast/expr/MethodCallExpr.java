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
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.ast.expr.NameExpr.*;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.none;

/**
 * @author Julio Vilmar Gesser
 */
public final class MethodCallExpr extends Expression implements 
        NodeWithTypeArguments<MethodCallExpr>,
        NodeWithArguments<MethodCallExpr> {

    private Optional<Expression> scope;

    private Optional<NodeList<Type<?>>> typeArguments;

    private NameExpr name;

    private NodeList<Expression> args;

    public MethodCallExpr() {
        this(Range.UNKNOWN,
                none(),
                none(),
                new NameExpr(),
                new NodeList<>());
    }

    public MethodCallExpr(final Optional<Expression> scope, final String name) {
        this(Range.UNKNOWN,
                scope,
                none(),
                name(name),
                new NodeList<>());
    }

    public MethodCallExpr(final Optional<Expression> scope, final NameExpr name, final NodeList<Expression> args) {
        this(Range.UNKNOWN,
                scope,
                none(),
                name,
                args);
    }

	public MethodCallExpr(final Range range, final Optional<Expression> scope, final Optional<NodeList<Type<?>>> typeArguments, final NameExpr name, final NodeList<Expression> args) {
		super(range);
		setScope(scope);
		setTypeArguments(typeArguments);
		setNameExpr(name);
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

    public String getName() {
        return name.getName();
    }

    public NameExpr getNameExpr() {
        return name;
    }

    public Optional<Expression> getScope() {
        return scope;
    }

    @Override
	public MethodCallExpr setArgs(final NodeList<Expression> args) {
		this.args = assertNotNull(args);
		setAsParentNodeOf(this.args);
        return this;
	}

    public MethodCallExpr setName(final String name) {
        setNameExpr(new NameExpr(assertNotNull(name)));
        return this;
    }

    public MethodCallExpr setNameExpr(NameExpr name) {
        this.name = assertNotNull(name);
        setAsParentNodeOf(this.name);
        return this;
    }

    public MethodCallExpr setScope(final Optional<Expression> scope) {
        this.scope = assertNotNull(scope);
        setAsParentNodeOf(this.scope);
        return this;
    }

    @Override
    public Optional<NodeList<Type<?>>> getTypeArguments() {
        return typeArguments;
    }

    @Override
    public MethodCallExpr setTypeArguments(final Optional<NodeList<Type<?>>> types) {
        this.typeArguments = assertNotNull(types);
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
