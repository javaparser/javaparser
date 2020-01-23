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
package org.javaparser.ast.stmt;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.expr.*;
import org.javaparser.ast.nodeTypes.NodeWithArguments;
import org.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import org.javaparser.ast.observer.ObservableProperty;
import org.javaparser.ast.type.Type;
import org.javaparser.ast.visitor.GenericVisitor;
import org.javaparser.ast.visitor.VoidVisitor;
import java.util.Optional;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.ast.Node;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.ExplicitConstructorInvocationStmtMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import org.javaparser.metamodel.OptionalProperty;
import org.javaparser.resolution.Resolvable;
import org.javaparser.resolution.UnsolvedSymbolException;
import org.javaparser.resolution.declarations.ResolvedConstructorDeclaration;
import java.util.function.Consumer;
import org.javaparser.ast.Generated;

/**
 * A call to super or this in a constructor or initializer.
 * <br/><code>class X { X() { super(15); } }</code>
 * <br/><code>class X { X() { this(1, 2); } }</code>
 *
 * @author Julio Vilmar Gesser
 * @see org.javaparser.ast.expr.SuperExpr
 * @see org.javaparser.ast.expr.ThisExpr
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
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public ExplicitConstructorInvocationStmt(TokenRange tokenRange, NodeList<Type> typeArguments, boolean isThis, Expression expression, NodeList<Expression> arguments) {
        super(tokenRange);
        setTypeArguments(typeArguments);
        setThis(isThis);
        setExpression(expression);
        setArguments(arguments);
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
    public NodeList<Expression> getArguments() {
        return arguments;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public Optional<Expression> getExpression() {
        return Optional.ofNullable(expression);
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public boolean isThis() {
        return isThis;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ExplicitConstructorInvocationStmt setArguments(final NodeList<Expression> arguments) {
        assertNotNull(arguments);
        if (arguments == this.arguments) {
            return (ExplicitConstructorInvocationStmt) this;
        }
        notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        if (this.arguments != null)
            this.arguments.setParentNode(null);
        this.arguments = arguments;
        setAsParentNodeOf(arguments);
        return this;
    }

    /**
     * Sets the expression
     *
     * @param expression the expression, can be null
     * @return this, the ExplicitConstructorInvocationStmt
     */
    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ExplicitConstructorInvocationStmt setExpression(final Expression expression) {
        if (expression == this.expression) {
            return (ExplicitConstructorInvocationStmt) this;
        }
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null)
            this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ExplicitConstructorInvocationStmt setThis(final boolean isThis) {
        if (isThis == this.isThis) {
            return (ExplicitConstructorInvocationStmt) this;
        }
        notifyPropertyChange(ObservableProperty.THIS, this.isThis, isThis);
        this.isThis = isThis;
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
     * @return this, the ExplicitConstructorInvocationStmt
     */
    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public ExplicitConstructorInvocationStmt setTypeArguments(final NodeList<Type> typeArguments) {
        if (typeArguments == this.typeArguments) {
            return (ExplicitConstructorInvocationStmt) this;
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
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.remove(i);
                return true;
            }
        }
        if (expression != null) {
            if (node == expression) {
                removeExpression();
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
    public ExplicitConstructorInvocationStmt removeExpression() {
        return setExpression((Expression) null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public ExplicitConstructorInvocationStmt clone() {
        return (ExplicitConstructorInvocationStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public ExplicitConstructorInvocationStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.explicitConstructorInvocationStmtMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < arguments.size(); i++) {
            if (arguments.get(i) == node) {
                arguments.set(i, (Expression) replacementNode);
                return true;
            }
        }
        if (expression != null) {
            if (node == expression) {
                setExpression((Expression) replacementNode);
                return true;
            }
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
    public boolean isExplicitConstructorInvocationStmt() {
        return true;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ExplicitConstructorInvocationStmt asExplicitConstructorInvocationStmt() {
        return this;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
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
    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ExplicitConstructorInvocationStmt> toExplicitConstructorInvocationStmt() {
        return Optional.of(this);
    }
}
