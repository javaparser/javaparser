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
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

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

    private Expression scope;

    private ClassOrInterfaceType type;

    private NodeList<Type<?>> typeArguments;

    private NodeList<Expression> args;

    private NodeList<BodyDeclaration<?>> anonymousClassBody;

    public ObjectCreationExpr() {
        this(null,
                null,
                new ClassOrInterfaceType(),
                new NodeList<>(),
                new NodeList<>(),
                null);
    }

    /**
     * Defines a call to a constructor.
     * 
     * @param scope may be null
     * @param type this is the class that the constructor is being called for.
     * @param args Any arguments to pass to the constructor
     */
    public ObjectCreationExpr(final Expression scope, final ClassOrInterfaceType type,
                              final NodeList<Expression> args) {
        this(null,
                scope,
                type,
                new NodeList<>(),
                args,
                null);
    }

    public ObjectCreationExpr(final Range range,
                              final Expression scope, final ClassOrInterfaceType type,
                              final NodeList<Type<?>> typeArguments,
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

    public Optional<NodeList<BodyDeclaration<?>>> getAnonymousClassBody() {
        return Optional.ofNullable(anonymousClassBody);
    }

    public void addAnonymousClassBody(BodyDeclaration<?> body) {
        if (anonymousClassBody == null)
            anonymousClassBody = new NodeList<>();
        anonymousClassBody.add(body);
    }

    @Override
    public NodeList<Expression> getArgs() {
        return args;
    }

    public Optional<Expression> getScope() {
        return Optional.ofNullable(scope);
    }

    @Override
    public ClassOrInterfaceType getType() {
        return type;
    }

    /**
     * Sets the anonymousClassBody<br>
     * Null means no class body<br>
     * Empty NodeList means new ClassName(){ }
     * 
     * @param anonymousClassBody the anonymousClassBody, can be null or empty
     * @return this, the ObjectCreationExpr
     */
    public ObjectCreationExpr setAnonymousClassBody(final NodeList<BodyDeclaration<?>> anonymousClassBody) {
        notifyPropertyChange(ObservableProperty.ANONYMOUS_CLASS_BODY, this.anonymousClassBody, anonymousClassBody);
        this.anonymousClassBody = anonymousClassBody;
        setAsParentNodeOf(this.anonymousClassBody);
        return this;
    }

    @Override
    public ObjectCreationExpr setArgs(final NodeList<Expression> args) {
        notifyPropertyChange(ObservableProperty.ARGS, this.args, args);
        this.args = assertNotNull(args);
        setAsParentNodeOf(this.args);
        return this;
    }

    /**
     * Sets the scope
     * 
     * @param scope the scope, can be null
     * @return this, the ObjectCreationExpr
     */
    public ObjectCreationExpr setScope(final Expression scope) {
        notifyPropertyChange(ObservableProperty.SCOPE, this.scope, scope);
        this.scope = scope;
        setAsParentNodeOf(this.scope);
        return this;
    }

    @Override
    public ObjectCreationExpr setType(final ClassOrInterfaceType type) {
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        assertNotNull(type);
        this.type = type;
        setAsParentNodeOf(this.type);
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
     * @return this, the ObjectCreationExpr
     */
    @Override
    public ObjectCreationExpr setTypeArguments(final NodeList<Type<?>> typeArguments) {
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        this.typeArguments = typeArguments;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
