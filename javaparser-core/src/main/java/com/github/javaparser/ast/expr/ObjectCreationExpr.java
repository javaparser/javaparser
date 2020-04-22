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
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithOptionalScope;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
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
import com.github.javaparser.TokenRange;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import java.util.function.Consumer;
import com.github.javaparser.ast.Generated;

/**
 * A constructor call.
 * <br>In {@code new HashMap.Entry<String, Long>(15) {public String getKey() {return null;}};}
 * HashMap.Entry is the type, String and Long are type arguments, 15 is an argument, and everything in { }
 * is the anonymous class body.
 * <p/>In {@code class B { class C { public void a() { new B().new C(); } } }} the scope is {@code new B()}
 * of ObjectCreationExpr {@code new B().new C()}
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
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ObjectCreationExpr(TokenRange tokenRange, Expression scope, ClassOrInterfaceType type, NodeList<Type> typeArguments, NodeList<Expression> arguments, NodeList<BodyDeclaration<?>> anonymousClassBody) {
        super(tokenRange);
        this.setScope(scope);
        this.setType(type);
        this.setTypeArguments(typeArguments);
        this.setArguments(arguments);
        this.setAnonymousClassBody(anonymousClassBody);
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
    public Optional<NodeList<BodyDeclaration<?>>> getAnonymousClassBody() {
        return Optional.ofNullable(this.anonymousClassBody);
    }

    public void addAnonymousClassBody(BodyDeclaration<?> body) {
        if (anonymousClassBody == null)
            anonymousClassBody = new NodeList<>();
        anonymousClassBody.add(body);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Expression> getArguments() {
        return this.arguments;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getScope() {
        return Optional.ofNullable(this.scope);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ClassOrInterfaceType getType() {
        return this.type;
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
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.ANONYMOUS_CLASS_BODY, this.anonymousClassBody, anonymousClassBody);
        if (this.anonymousClassBody != null) {
            this.anonymousClassBody.setParentNode(null);
        }
        this.anonymousClassBody = anonymousClassBody;
        this.setAsParentNodeOf(anonymousClassBody);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ObjectCreationExpr setArguments(final NodeList<Expression> arguments) {
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

    /**
     * Sets the scope
     *
     * @param scope the scope, can be null
     * @return this, the ObjectCreationExpr
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ObjectCreationExpr setScope(final Expression scope) {
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
    public ObjectCreationExpr setType(final ClassOrInterfaceType type) {
        assertNotNull(type);
        if (type == this.type) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null) {
            this.type.setParentNode(null);
        }
        this.type = type;
        this.setAsParentNodeOf(type);
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
     * @return this, the ObjectCreationExpr
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ObjectCreationExpr setTypeArguments(final NodeList<Type> typeArguments) {
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
        if (this.anonymousClassBody != null) {
            for (int i = 0; i < this.anonymousClassBody.size(); i++) {
                if (this.anonymousClassBody.get(i) == node) {
                    this.anonymousClassBody.remove(i);
                    return true;
                }
            }
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
    public ObjectCreationExpr removeScope() {
        return this.setScope((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ObjectCreationExpr clone() {
        return (ObjectCreationExpr) this.accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ObjectCreationExprMetaModel getMetaModel() {
        return JavaParserMetaModel.objectCreationExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        if (this.anonymousClassBody != null) {
            for (int i = 0; i < this.anonymousClassBody.size(); i++) {
                if (this.anonymousClassBody.get(i) == node) {
                    this.anonymousClassBody.set(i, (BodyDeclaration) replacementNode);
                    return true;
                }
            }
        }
        for (int i = 0; i < this.arguments.size(); i++) {
            if (this.arguments.get(i) == node) {
                this.arguments.set(i, (Expression) replacementNode);
                return true;
            }
        }
        if (this.scope != null) {
            if (node == this.scope) {
                this.setScope((Expression) replacementNode);
                return true;
            }
        }
        if (node == this.type) {
            this.setType((ClassOrInterfaceType) replacementNode);
            return true;
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
    public boolean isObjectCreationExpr() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ObjectCreationExpr asObjectCreationExpr() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
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
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ObjectCreationExpr> toObjectCreationExpr() {
        return Optional.of(this);
    }
}
