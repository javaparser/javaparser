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
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.utils.Utils.ensureNotNull;

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
        NodeWithType<ObjectCreationExpr> {

    private Expression scope;

    private ClassOrInterfaceType type;

    private List<Type<?>> typeArguments;

    private List<Expression> args;

    // This can be null, to indicate there is no body
    private List<BodyDeclaration<?>> anonymousClassBody;

    public ObjectCreationExpr() {
    }

    /**
     * Defines a call to a constructor.
     * 
     * @param scope may be null
     * @param type this is the class that the constructor is being called for.
     * @param args Any arguments to pass to the constructor
     */
    public ObjectCreationExpr(final Expression scope, final ClassOrInterfaceType type, final List<Expression> args) {
        setScope(scope);
        setType(type);
        setArgs(args);
    }

	public ObjectCreationExpr(final Range range,
			final Expression scope, final ClassOrInterfaceType type, final List<Type<?>> typeArguments,
                              final List<Expression> args, final List<BodyDeclaration<?>> anonymousBody) {
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
    public List<BodyDeclaration<?>> getAnonymousClassBody() {
        return anonymousClassBody;
    }

    public void addAnonymousClassBody(BodyDeclaration<?> body) {
        if (anonymousClassBody == null)
            anonymousClassBody = new ArrayList<>();
        anonymousClassBody.add(body);
        body.setParentNode(this);
    }

    public List<Expression> getArgs() {
        args = ensureNotNull(args);
        return args;
    }

    public Expression getScope() {
        return scope;
    }

    @Override
    public ClassOrInterfaceType getType() {
        return type;
    }

    public ObjectCreationExpr setAnonymousClassBody(final List<BodyDeclaration<?>> anonymousClassBody) {
        this.anonymousClassBody = anonymousClassBody;
        setAsParentNodeOf(this.anonymousClassBody);
        return this;
    }

    public ObjectCreationExpr setArgs(final List<Expression> args) {
        this.args = args;
        setAsParentNodeOf(this.args);
        return this;
    }

    public ObjectCreationExpr setScope(final Expression scope) {
        this.scope = scope;
        setAsParentNodeOf(this.scope);
        return this;
    }

    @Override
    public ObjectCreationExpr setType(final Type<?> type) {
        if (!(type instanceof ClassOrInterfaceType))// needed so we can use NodeWithType
            throw new RuntimeException("You can only add ClassOrInterfaceType to an ObjectCreationExpr");
        this.type = (ClassOrInterfaceType) type;
        setAsParentNodeOf(this.type);
        return this;
    }

    @Override
    public List<Type<?>> getTypeArguments() {
        return typeArguments;
    }

    @Override
    public ObjectCreationExpr setTypeArguments(final List<Type<?>> types) {
        this.typeArguments = types;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
