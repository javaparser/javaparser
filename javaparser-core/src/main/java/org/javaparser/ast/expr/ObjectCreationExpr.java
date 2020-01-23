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
package org.javaparser.ast.expr;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.body.BodyDeclaration;
import org.javaparser.ast.nodeTypes.NodeWithArguments;
import org.javaparser.ast.nodeTypes.NodeWithOptionalScope;
import org.javaparser.ast.nodeTypes.NodeWithType;
import org.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import org.javaparser.ast.type.ClassOrInterfaceType;
import org.javaparser.ast.type.Type;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.ObjectCreationExprMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import org.javaparser.metamodel.OptionalProperty;
import org.javaparser.resolution.Resolvable;
import org.javaparser.resolution.UnsolvedSymbolException;
import org.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import java.util.function.Consumer;
import org.javaparser.ast.Generated;

/**
 * A constructor call.
 * <br/>In <code>new HashMap.Entry&lt;String, Long>(15) {public String getKey() {return null;}};</code>
 * HashMap.Entry is the type, String and Long are type arguments, 15 is an argument, and everything in { }
 * is the anonymous class body.
 * <p/>In <code>class B { class C { public void a() { new B().new C(); } } }</code> the scope is <code>new B()</code>
 * of ObjectCreationExpr <code>new B().new C()</code>
 *
 * @author Julio Vilmar Gesser
 */
public class ObjectCreationExpr extends Expression implements NodeWithTypeArguments<ObjectCreationExpr>, NodeWithType<ObjectCreationExpr, ClassOrInterfaceType>, NodeWithArguments<ObjectCreationExpr>, NodeWithOptionalScope<ObjectCreationExpr>, Resolvable<ResolvedConstructorDeclaration> {

    @OptionalProperty
    private Expression scope;

    private ClassOrInterfaceType type;

    @OptionalProperty
    private NodeList<Type> typeArguments;

    private NodeList<Expression> arguments;

    @OptionalProperty
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
        this(null, scope, type, null, arguments, null);
    }

    @AllFieldsConstructor
    public ObjectCreationExpr(final Expression scope, final ClassOrInterfaceType type, final NodeList<Type> typeArguments, final NodeList<Expression> arguments, final NodeList<BodyDeclaration<?>> anonymousClassBody) {
        this(null, scope, type, typeArguments, arguments, anonymousClassBody);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public ObjectCreationExpr(TokenRange tokenRange, Expression scope, ClassOrInterfaceType type, NodeList<Type> typeArguments, NodeList<Expression> arguments, NodeList<BodyDeclaration<?>> anonymousClassBody) {
        super(tokenRange);
        setScope(scope);
        setType(type);
        setTypeArguments(typeArguments);
        setArguments(arguments);
        setAnonymousClassBody(anonymousClassBody);
        customInitialization();
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Optional<NodeList<BodyDeclaration<?>>> getAnonymousClassBody() {
        return Optional.ofNullable(anonymousClassBody);
    }

    public void addAnonymousClassBody(BodyDeclaration<?> body) {
        if (anonymousClassBody == null)
            anonymousClassBody = new NodeList<>();
        anonymousClassBody.add(body);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getArguments() {
        return arguments;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getScope() {
        return Optional.ofNullable(scope);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
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
    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ObjectCreationExpr setAnonymousClassBody(final NodeList<BodyDeclaration<?>> anonymousClassBody) {
        if (anonymousClassBody == this.anonymousClassBody) {
            return (ObjectCreationExpr) this;
        }
        notifyPropertyChange(ObservableProperty.ANONYMOUS_CLASS_BODY, this.anonymousClassBody, anonymousClassBody);
        if (this.anonymousClassBody != null)
            this.anonymousClassBody.setParentNode(null);
        this.anonymousClassBody = anonymousClassBody;
        setAsParentNodeOf(anonymousClassBody);
        return this;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ObjectCreationExpr setArguments(final NodeList<Expression> arguments) {
        assertNotNull(arguments);
        if (arguments == this.arguments) {
            return (ObjectCreationExpr) this;
        }
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
    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ObjectCreationExpr setScope(final Expression scope) {
        if (scope == this.scope) {
            return (ObjectCreationExpr) this;
        }
        notifyPropertyChange(ObservableProperty.SCOPE, this.scope, scope);
        if (this.scope != null)
            this.scope.setParentNode(null);
        this.scope = scope;
        setAsParentNodeOf(scope);
        return this;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ObjectCreationExpr setType(final ClassOrInterfaceType type) {
        assertNotNull(type);
        if (type == this.type) {
            return (ObjectCreationExpr) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Optional<NodeList<Type>> getTypeArguments() {
        return Optional.ofNullable(typeArguments);
    }

    /**
     * Sets the typeArguments
     *
     * @param typeArguments the typeArguments, can be null
     * @return this, the ObjectCreationExpr
     */
    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ObjectCreationExpr setTypeArguments(final NodeList<Type> typeArguments) {
        if (typeArguments == this.typeArguments) {
            return (ObjectCreationExpr) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        if (this.typeArguments != null)
            this.typeArguments.setParentNode(null);
        this.typeArguments = typeArguments;
        setAsParentNodeOf(typeArguments);
        return this;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
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

    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public ObjectCreationExpr removeScope() {
        return setScope((Expression) null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public ObjectCreationExpr clone() {
        return (ObjectCreationExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public ObjectCreationExprMetaModel getMetaModel() {
        return JavaParserMetaModel.objectCreationExprMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (anonymousClassBody != null) {
            for (int i = 0; i < anonymousClassBody.size(); i++) {
                if (anonymousClassBody.get(i) == node) {
                    anonymousClassBody.set(i, (BodyDeclaration) replacementNode);
                    return true;
                }
            }
        }
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.set(i, (Expression) replacementNode);
                return true;
            }
        }
        if (scope != null) {
            if (node == scope) {
                setScope((Expression) replacementNode);
                return true;
            }
        }
        if (node == type) {
            setType((ClassOrInterfaceType) replacementNode);
            return true;
        }
        if (typeArguments != null) {
            for (int i = 0; i < typeArguments.size(); i++) {
                if (typeArguments.get(i) == node) {
                    typeArguments.set(i, (Type) replacementNode);
                    return true;
                }
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isObjectCreationExpr() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ObjectCreationExpr asObjectCreationExpr() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifObjectCreationExpr(Consumer<ObjectCreationExpr> action) {
        action.accept(this);
    }

    /**
     * Attempts to resolve the declaration corresponding to the invoked constructor. If successful, a
     * {@link ResolvedConstructorDeclaration} representing the declaration of the constructor invoked by this
     * {@code ObjectCreationExpr} is returned. Otherwise, an {@link UnsolvedSymbolException} is thrown.
     *
     * @return a {@link ResolvedConstructorDeclaration} representing the declaration of the invoked constructor.
     * @throws UnsolvedSymbolException if the declaration corresponding to the object creation expression could not be
     *                                 resolved.
     * @see NameExpr#resolve()
     * @see FieldAccessExpr#resolve()
     * @see MethodCallExpr#resolve()
     * @see ExplicitConstructorInvocationStmt#resolve()
     */
    @Override
    public ResolvedConstructorDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedConstructorDeclaration.class);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ObjectCreationExpr> toObjectCreationExpr() {
        return Optional.of(this);
    }
}
