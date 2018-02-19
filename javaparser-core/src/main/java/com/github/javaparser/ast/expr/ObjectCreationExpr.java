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
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ObjectCreationExprMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import java.util.function.Consumer;

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
public final class ObjectCreationExpr extends Expression implements NodeWithTypeArguments<ObjectCreationExpr>, NodeWithType<ObjectCreationExpr, ClassOrInterfaceType>, NodeWithArguments<ObjectCreationExpr>, NodeWithOptionalScope<ObjectCreationExpr> {

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
        this(null, scope, type, new NodeList<>(), arguments, null);
    }

    @AllFieldsConstructor
    public ObjectCreationExpr(final Expression scope, final ClassOrInterfaceType type, final NodeList<Type> typeArguments, final NodeList<Expression> arguments, final NodeList<BodyDeclaration<?>> anonymousClassBody) {
        this(null, scope, type, typeArguments, arguments, anonymousClassBody);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
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
    public Optional<NodeList<BodyDeclaration<?>>> getAnonymousClassBody() {
        return Optional.ofNullable(anonymousClassBody);
    }

    public void addAnonymousClassBody(BodyDeclaration<?> body) {
        if (anonymousClassBody == null)
            anonymousClassBody = new NodeList<>();
        anonymousClassBody.add(body);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getArguments() {
        return arguments;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getScope() {
        return Optional.ofNullable(scope);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<NodeList<Type>> getTypeArguments() {
        return Optional.ofNullable(typeArguments);
    }

    /**
     * Sets the typeArguments
     *
     * @param typeArguments the typeArguments, can be null
     * @return this, the ObjectCreationExpr
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
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

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public ObjectCreationExpr removeScope() {
        return setScope((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ObjectCreationExpr clone() {
        return (ObjectCreationExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ObjectCreationExprMetaModel getMetaModel() {
        return JavaParserMetaModel.objectCreationExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isObjectCreationExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ObjectCreationExpr asObjectCreationExpr() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifObjectCreationExpr(Consumer<ObjectCreationExpr> action) {
        action.accept(this);
    }

    public ResolvedConstructorDeclaration resolveInvokedConstructor() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedConstructorDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ObjectCreationExpr> toObjectCreationExpr() {
        return Optional.of(this);
    }
}
