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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalScope;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;

/**
 * A constructor call. <br/>In <code>new HashMap.Entry<String, Long>(15) {public String getKey() {return null;}};</code>
 * HashMap is the scope, Entry is the type, String and Long are type arguments, 15 is an argument, and everything in { }
 * is the anonymous class body.
 *
 * @author Julio Vilmar Gesser
 */
public final class ObjectCreationExpr extends Expression implements NodeWithTypeArguments<ObjectCreationExpr>, NodeWithType<ObjectCreationExpr, ClassOrInterfaceType>, NodeWithArguments<ObjectCreationExpr>, NodeWithOptionalScope<ObjectCreationExpr> {

    private Expression scope;

    private ClassOrInterfaceType type;

    private NodeList<Type> typeArguments;

    private NodeList<Expression> arguments;

    private NodeList<BodyDeclaration<?>> anonymousClassBody;

    public ObjectCreationExpr() {
        this(null, null, new ClassOrInterfaceType(), new NodeList<>(), new NodeList<>(), null);
    }

    /**
     * Defines a call to a constructor.
     *
     * @param scope may be null
     * @param type this is the class that the constructor is being called for.
     * @param arguments Any arguments to pass to the constructor
     */
    public ObjectCreationExpr(final Expression scope, final ClassOrInterfaceType type, final NodeList<Expression> arguments) {
        this(null, scope, type, new NodeList<>(), arguments, null);
    }

    @AllFieldsConstructor
    public ObjectCreationExpr(final Expression scope, final ClassOrInterfaceType type, final NodeList<Type> typeArguments, final NodeList<Expression> arguments, final NodeList<BodyDeclaration<?>> anonymousClassBody) {
        this(null, scope, type, typeArguments, arguments, anonymousClassBody);
    }

    public ObjectCreationExpr(final Range range, final Expression scope, final ClassOrInterfaceType type, final NodeList<Type> typeArguments, final NodeList<Expression> arguments, final NodeList<BodyDeclaration<?>> anonymousClassBody) {
        super(range);
        setScope(scope);
        setType(type);
        setTypeArguments(typeArguments);
        setArguments(arguments);
        setAnonymousClassBody(anonymousClassBody);
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
    public NodeList<Expression> getArguments() {
        return arguments;
    }

    @Override
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
        if (this.anonymousClassBody != null)
            this.anonymousClassBody.setParentNode(null);
        this.anonymousClassBody = anonymousClassBody;
        setAsParentNodeOf(anonymousClassBody);
        return this;
    }

    @Override
    public ObjectCreationExpr setArguments(final NodeList<Expression> arguments) {
        assertNotNull(arguments);
        notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        if (this.arguments != null)
            this.arguments.setParentNode(null);
        this.arguments = arguments;
        setAsParentNodeOf(arguments);
        return this;
    }

    /**
     * Sets the scope
     *
     * @param scope the scope, can be null
     * @return this, the ObjectCreationExpr
     */
    @Override
    public ObjectCreationExpr setScope(final Expression scope) {
        notifyPropertyChange(ObservableProperty.SCOPE, this.scope, scope);
        if (this.scope != null)
            this.scope.setParentNode(null);
        this.scope = scope;
        setAsParentNodeOf(scope);
        return this;
    }

    @Override
    public ObjectCreationExpr setType(final ClassOrInterfaceType type) {
        assertNotNull(type);
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
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
     * @return this, the ObjectCreationExpr
     */
    @Override
    public ObjectCreationExpr setTypeArguments(final NodeList<Type> typeArguments) {
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        if (this.typeArguments != null)
            this.typeArguments.setParentNode(null);
        this.typeArguments = typeArguments;
        setAsParentNodeOf(typeArguments);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getAnonymousClassBody().orElse(null), getArguments(), getTypeArguments().orElse(null));
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (anonymousClassBody != null) {
            for (int i = 0; i < anonymousClassBody.size(); i++) {
                if (anonymousClassBody.get(i) == node) {
                    anonymousClassBody.remove(i);
                    return true;
                }
            }
        }
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.remove(i);
                return true;
            }
        }
        if (scope != null) {
            if (node == scope) {
                removeScope();
                return true;
            }
        }
        if (typeArguments != null) {
            for (int i = 0; i < typeArguments.size(); i++) {
                if (typeArguments.get(i) == node) {
                    typeArguments.remove(i);
                    return true;
                }
            }
        }
        return super.remove(node);
    }

    public ObjectCreationExpr removeScope() {
        return setScope((Expression) null);
    }
}

