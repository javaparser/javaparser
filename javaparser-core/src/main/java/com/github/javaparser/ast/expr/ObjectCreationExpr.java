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
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Defines constructor call expression.
 * Example:
 * <code>
 *     new Object()
 * </code>
 *
 * @author Julio Vilmar Gesser
 */
public final class ObjectCreationExpr extends Expression implements 
        NodeWithTypeArguments<ObjectCreationExpr>,
        NodeWithType<ObjectCreationExpr, ClassOrInterfaceType>,
        NodeWithArguments<ObjectCreationExpr> {

    // TODO nullable
    private Expression scope;

    private ClassOrInterfaceType type;

    private NodeList<Type<?>> typeArguments;

    private NodeList<Expression> args;

    // TODO This can be null, to indicate there is no body
    private NodeList<BodyDeclaration<?>> anonymousClassBody = null;

    public ObjectCreationExpr() {
        this(Range.UNKNOWN, 
                null,
                new ClassOrInterfaceType(),
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>());
    }

    /**
     * Defines a call to a constructor.
     * 
     * @param scope may be null
     * @param type this is the class that the constructor is being called for.
     * @param args Any arguments to pass to the constructor
     */
    public ObjectCreationExpr(final Expression scope, final ClassOrInterfaceType type, final NodeList<Expression> args) {
        this(Range.UNKNOWN,
                scope,
                type,
                new NodeList<>(),
                args,
                new NodeList<>());
    }

	public ObjectCreationExpr(final Range range,
			final Expression scope, final ClassOrInterfaceType type, final NodeList<Type<?>> typeArguments,
                              final NodeList<Expression> args, final NodeList<BodyDeclaration<?>> anonymousBody) {
		super(range);
		setScope(scope);
		setType(type);
		setTypeArguments(typeArguments);
		setArgs(args);
		setAnonymousClassBody(anonymousBody);
	}

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    /**
     * This can be null, to indicate there is no body
     */
    public NodeList<BodyDeclaration<?>> getAnonymousClassBody() {
        return anonymousClassBody;
    }

    public void addAnonymousClassBody(BodyDeclaration<?> body) {
        if (anonymousClassBody == null)
            anonymousClassBody = new NodeList<>();
        anonymousClassBody.add(body);
    }

    public NodeList<Expression> getArgs() {
        return args;
    }

    public Expression getScope() {
        return scope;
    }

    @Override
    public ClassOrInterfaceType getType() {
        return type;
    }

    public ObjectCreationExpr setAnonymousClassBody(final NodeList<BodyDeclaration<?>> anonymousClassBody) {
        this.anonymousClassBody = anonymousClassBody;
        setAsParentNodeOf(this.anonymousClassBody);
        return this;
    }

    @Override
    public ObjectCreationExpr setArgs(final NodeList<Expression> args) {
        this.args = assertNotNull(args);
        setAsParentNodeOf(this.args);
        return this;
    }

    public ObjectCreationExpr setScope(final Expression scope) {
        this.scope = scope;
        setAsParentNodeOf(this.scope);
        return this;
    }

    @Override
    public ObjectCreationExpr setType(final ClassOrInterfaceType type) {
        assertNotNull(type);
        this.type = type;
        setAsParentNodeOf(this.type);
        return this;
    }

    @Override
    public NodeList<Type<?>> getTypeArguments() {
        return typeArguments;
    }

    @Override
    public ObjectCreationExpr setTypeArguments(final NodeList<Type<?>> typeArguments) {
        this.typeArguments = typeArguments;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
