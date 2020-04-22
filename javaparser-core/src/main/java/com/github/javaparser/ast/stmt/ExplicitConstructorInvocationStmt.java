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
package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ExplicitConstructorInvocationStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.TokenRange;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import java.util.function.Consumer;
import com.github.javaparser.ast.Generated;

/**
 * A call to super or this in a constructor or initializer.
 * <br>{@code class X { X() { super(15); } }}
 * <br>{@code class X { X() { this(1, 2); } }}
 *
 * @author Julio Vilmar Gesser
 * @see com.github.javaparser.ast.expr.SuperExpr
 * @see com.github.javaparser.ast.expr.ThisExpr
 */
public class ExplicitConstructorInvocationStmt extends Statement implements NodeWithTypeArguments<ExplicitConstructorInvocationStmt>, NodeWithArguments<ExplicitConstructorInvocationStmt>, Resolvable<ResolvedConstructorDeclaration> {

    @OptionalProperty
    private NodeList<Type> typeArguments;

    private boolean isThis;

    @OptionalProperty
    private Expression expression;

    private NodeList<Expression> arguments;

    public ExplicitConstructorInvocationStmt() {
        this(null, null, true, null, new NodeList<>());
    }

    public ExplicitConstructorInvocationStmt(final boolean isThis, final Expression expression, final NodeList<Expression> arguments) {
        this(null, null, isThis, expression, arguments);
    }

    @AllFieldsConstructor
    public ExplicitConstructorInvocationStmt(final NodeList<Type> typeArguments, final boolean isThis, final Expression expression, final NodeList<Expression> arguments) {
        this(null, typeArguments, isThis, expression, arguments);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ExplicitConstructorInvocationStmt(TokenRange tokenRange, NodeList<Type> typeArguments, boolean isThis, Expression expression, NodeList<Expression> arguments) {
        super(tokenRange);
        this.setTypeArguments(typeArguments);
        this.setThis(isThis);
        this.setExpression(expression);
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
    public Optional<Expression> getExpression() {
        return Optional.ofNullable(this.expression);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public boolean isThis() {
        return this.isThis;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ExplicitConstructorInvocationStmt setArguments(final NodeList<Expression> arguments) {
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
     * Sets the expression
     *
     * @param expression the expression, can be null
     * @return this, the ExplicitConstructorInvocationStmt
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ExplicitConstructorInvocationStmt setExpression(final Expression expression) {
        if (expression == this.expression) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null) {
            this.expression.setParentNode(null);
        }
        this.expression = expression;
        this.setAsParentNodeOf(expression);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ExplicitConstructorInvocationStmt setThis(final boolean isThis) {
        if (isThis == this.isThis) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.THIS, this.isThis, isThis);
        this.isThis = isThis;
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
     * @return this, the ExplicitConstructorInvocationStmt
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ExplicitConstructorInvocationStmt setTypeArguments(final NodeList<Type> typeArguments) {
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
        if (this.expression != null) {
            if (node == this.expression) {
                this.removeExpression();
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
    public ExplicitConstructorInvocationStmt removeExpression() {
        return this.setExpression((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ExplicitConstructorInvocationStmt clone() {
        return (ExplicitConstructorInvocationStmt) this.accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ExplicitConstructorInvocationStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.explicitConstructorInvocationStmtMetaModel;
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
        if (this.expression != null) {
            if (node == this.expression) {
                this.setExpression((Expression) replacementNode);
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
    public boolean isExplicitConstructorInvocationStmt() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ExplicitConstructorInvocationStmt asExplicitConstructorInvocationStmt() {
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifExplicitConstructorInvocationStmt(Consumer<ExplicitConstructorInvocationStmt> action) {
        action.accept(this);
    }

    /**
     * Attempts to resolve the declaration corresponding to the invoked constructor. If successful, a
     * {@link ResolvedConstructorDeclaration} representing the declaration of the constructor invoked by this
     * {@code ExplicitConstructorInvocationStmt} is returned. Otherwise, an {@link UnsolvedSymbolException} is thrown.
     *
     * @return a {@link ResolvedConstructorDeclaration} representing the declaration of the invoked constructor.
     * @throws UnsolvedSymbolException if the declaration corresponding to the explicit constructor invocation statement
     *                                 could not be resolved.
     * @see NameExpr#resolve()
     * @see FieldAccessExpr#resolve()
     * @see MethodCallExpr#resolve()
     * @see ObjectCreationExpr#resolve()
     */
    public ResolvedConstructorDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedConstructorDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ExplicitConstructorInvocationStmt> toExplicitConstructorInvocationStmt() {
        return Optional.of(this);
    }
}
