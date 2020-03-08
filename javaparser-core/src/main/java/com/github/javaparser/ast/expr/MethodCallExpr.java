/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalScope;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.MethodCallExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedMethodDeclaration;
import java.util.function.Consumer;
import com.github.javaparser.ast.Generated;

/**
 * A method call on an object or a class. <br/><code>circle.circumference()</code> <br/>In <code>a.&lt;String&gt;bb(15);</code> a
 * is the scope, String is a type argument, bb is the name and 15 is an argument.
 *
 * @author Julio Vilmar Gesser
 */
public class MethodCallExpr extends Expression implements NodeWithTypeArguments<MethodCallExpr>, NodeWithArguments<MethodCallExpr>, NodeWithSimpleName<MethodCallExpr>, NodeWithOptionalScope<MethodCallExpr>, Resolvable<ResolvedMethodDeclaration> {

    @OptionalProperty
    private Expression scope;

    @OptionalProperty
    private NodeList<Type> typeArguments;

    private SimpleName name;

    private NodeList<Expression> arguments;

    public MethodCallExpr() {
        this(null, null, null, new SimpleName(), new NodeList<>());
    }

    public MethodCallExpr(String name, Expression... arguments) {
        this(null, null, null, new SimpleName(name), new NodeList<>(arguments));
    }

    public MethodCallExpr(final Expression scope, final String name) {
        this(null, scope, null, new SimpleName(name), new NodeList<>());
    }

    public MethodCallExpr(final Expression scope, final SimpleName name) {
        this(null, scope, null, name, new NodeList<>());
    }

    public MethodCallExpr(final Expression scope, final String name, final NodeList<Expression> arguments) {
        this(null, scope, null, new SimpleName(name), arguments);
    }

    public MethodCallExpr(final Expression scope, final NodeList<Type> typeArguments, final String name, final NodeList<Expression> arguments) {
        this(null, scope, typeArguments, new SimpleName(name), arguments);
    }

    public MethodCallExpr(final Expression scope, final SimpleName name, final NodeList<Expression> arguments) {
        this(null, scope, null, name, arguments);
    }

    @AllFieldsConstructor
    public MethodCallExpr(final Expression scope, final NodeList<Type> typeArguments, final SimpleName name, final NodeList<Expression> arguments) {
        this(null, scope, typeArguments, name, arguments);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public MethodCallExpr(TokenRange tokenRange, Expression scope, NodeList<Type> typeArguments, SimpleName name, NodeList<Expression> arguments) {
        super(tokenRange);
        this.setScope(scope);
        this.setTypeArguments(typeArguments);
        this.setName(name);
        this.setArguments(arguments);
        this.customInitialization();
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
    public NodeList<Expression> getArguments() {
        return this.arguments;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return this.name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getScope() {
        return Optional.ofNullable(this.scope);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public MethodCallExpr setArguments(final NodeList<Expression> arguments) {
        assertNotNull(arguments);
        if (arguments == this.arguments) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        if (this.arguments != null) {
            this.arguments.setParentNode(null);
        }
        this.arguments = arguments;
        this.setAsParentNodeOf(arguments);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public MethodCallExpr setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null) {
            this.name.setParentNode(null);
        }
        this.name = name;
        this.setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public MethodCallExpr setScope(final Expression scope) {
        if (scope == this.scope) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.SCOPE, this.scope, scope);
        if (this.scope != null) {
            this.scope.setParentNode(null);
        }
        this.scope = scope;
        this.setAsParentNodeOf(scope);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<NodeList<Type>> getTypeArguments() {
        return Optional.ofNullable(this.typeArguments);
    }

    /**
     * Sets the typeArguments
     *
     * @param typeArguments the typeArguments, can be null
     * @return this, the MethodCallExpr
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public MethodCallExpr setTypeArguments(final NodeList<Type> typeArguments) {
        if (typeArguments == this.typeArguments) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        if (this.typeArguments != null) {
            this.typeArguments.setParentNode(null);
        }
        this.typeArguments = typeArguments;
        this.setAsParentNodeOf(typeArguments);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < this.arguments.size(); i++) {
            if (this.arguments.get(i) == node) {
                this.arguments.remove(i);
                return true;
            }
        }
        if (this.scope != null) {
            if (node == this.scope) {
                this.removeScope();
                return true;
            }
        }
        if (this.typeArguments != null) {
            for (int i = 0; i < this.typeArguments.size(); i++) {
                if (this.typeArguments.get(i) == node) {
                    this.typeArguments.remove(i);
                    return true;
                }
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public MethodCallExpr removeScope() {
        return this.setScope((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public MethodCallExpr clone() {
        return (MethodCallExpr) this.accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public MethodCallExprMetaModel getMetaModel() {
        return JavaParserMetaModel.methodCallExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < this.arguments.size(); i++) {
            if (this.arguments.get(i) == node) {
                this.arguments.set(i, (Expression) replacementNode);
                return true;
            }
        }
        if (node == this.name) {
            this.setName((SimpleName) replacementNode);
            return true;
        }
        if (this.scope != null) {
            if (node == this.scope) {
                this.setScope((Expression) replacementNode);
                return true;
            }
        }
        if (this.typeArguments != null) {
            for (int i = 0; i < this.typeArguments.size(); i++) {
                if (this.typeArguments.get(i) == node) {
                    this.typeArguments.set(i, (Type) replacementNode);
                    return true;
                }
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMethodCallExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public MethodCallExpr asMethodCallExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMethodCallExpr(Consumer<MethodCallExpr> action) {
        action.accept(this);
    }

    /**
     * Attempts to resolve the declaration corresponding to the invoked method. If successful, a
     * {@link ResolvedMethodDeclaration} representing the declaration of the constructor invoked by this
     * {@code MethodCallExpr} is returned. Otherwise, an {@link UnsolvedSymbolException} is thrown.
     *
     * @return a {@link ResolvedMethodDeclaration} representing the declaration of the invoked method.
     * @throws UnsolvedSymbolException if the declaration corresponding to the method call expression could not be
     *                                 resolved.
     * @see NameExpr#resolve()
     * @see FieldAccessExpr#resolve()
     * @see ObjectCreationExpr#resolve()
     * @see ExplicitConstructorInvocationStmt#resolve()
     */
    @Override
    public ResolvedMethodDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedMethodDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<MethodCallExpr> toMethodCallExpr() {
        return Optional.of(this);
    }
}
