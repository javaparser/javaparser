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

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.none;
import static com.github.javaparser.utils.Utils.some;

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

    private Optional<Expression> scope;

    private ClassOrInterfaceType type;

    private Optional<NodeList<Type<?>>> typeArguments;

    private NodeList<Expression> args;

    private Optional<NodeList<BodyDeclaration<?>>> anonymousClassBody = null;

    public ObjectCreationExpr() {
        this(Range.UNKNOWN, 
                none(),
                new ClassOrInterfaceType(),
                none(),
                new NodeList<>(),
                none());
    }

    /**
     * Defines a call to a constructor.
     * 
     * @param scope may be null
     * @param type this is the class that the constructor is being called for.
     * @param args Any arguments to pass to the constructor
     */
    public ObjectCreationExpr(final Optional<Expression> scope, final ClassOrInterfaceType type, final NodeList<Expression> args) {
        this(Range.UNKNOWN,
                scope,
                type,
                none(),
                args,
                none());
    }

	public ObjectCreationExpr(final Range range,
			final Optional<Expression> scope, final ClassOrInterfaceType type, final Optional<NodeList<Type<?>>> typeArguments,
                              final NodeList<Expression> args, final Optional<NodeList<BodyDeclaration<?>>> anonymousBody) {
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
    public Optional<NodeList<BodyDeclaration<?>>> getAnonymousClassBody() {
        return anonymousClassBody;
    }

    public void addAnonymousClassBody(BodyDeclaration<?> body) {
        if(!anonymousClassBody.isPresent()){
            anonymousClassBody = some(new NodeList<>());
        }
        anonymousClassBody.get().add(body);
    }

    public NodeList<Expression> getArgs() {
        return args;
    }

    public Optional<Expression> getScope() {
        return scope;
    }

    @Override
    public ClassOrInterfaceType getType() {
        return type;
    }

    public ObjectCreationExpr setAnonymousClassBody(final Optional<NodeList<BodyDeclaration<?>>> anonymousClassBody) {
        this.anonymousClassBody = assertNotNull(anonymousClassBody);
        setAsParentNodeOf(this.anonymousClassBody);
        return this;
    }

    @Override
    public ObjectCreationExpr setArgs(final NodeList<Expression> args) {
        this.args = assertNotNull(args);
        setAsParentNodeOf(this.args);
        return this;
    }

    public ObjectCreationExpr setScope(final Optional<Expression> scope) {
        this.scope = assertNotNull(scope);
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
    public Optional<NodeList<Type<?>>> getTypeArguments() {
        return typeArguments;
    }

    @Override
    public ObjectCreationExpr setTypeArguments(final Optional<NodeList<Type<?>>> typeArguments) {
        this.typeArguments = assertNotNull(typeArguments);
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
