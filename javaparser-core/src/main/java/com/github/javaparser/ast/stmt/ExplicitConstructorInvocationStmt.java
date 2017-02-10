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
package com.github.javaparser.ast.stmt;

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.ExplicitConstructorInvocationStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A call to super or this in a constructor or initializer.
 * <br/><code>class X { X() { super(15); } }</code>
 * <br/><code>class X { X() { this(1, 2); } }</code>
 *
 * @author Julio Vilmar Gesser
 * @see com.github.javaparser.ast.expr.SuperExpr
 * @see com.github.javaparser.ast.expr.ThisExpr
 */
public final class ExplicitConstructorInvocationStmt extends Statement implements NodeWithTypeArguments<ExplicitConstructorInvocationStmt> {

    private NodeList<Type> typeArguments;

    private boolean isThis;

    private Expression expression;

    private NodeList<Expression> arguments;

    public ExplicitConstructorInvocationStmt() {
        this(null, new NodeList<>(), true, null, new NodeList<>());
    }

    public ExplicitConstructorInvocationStmt(final boolean isThis, final Expression expression, final NodeList<Expression> arguments) {
        this(null, new NodeList<>(), isThis, expression, arguments);
    }

    @AllFieldsConstructor
    public ExplicitConstructorInvocationStmt(final NodeList<Type> typeArguments, final boolean isThis, final Expression expression, final NodeList<Expression> arguments) {
        this(null, typeArguments, isThis, expression, arguments);
    }

    public ExplicitConstructorInvocationStmt(Range range, final NodeList<Type> typeArguments, final boolean isThis, final Expression expression, final NodeList<Expression> arguments) {
        super(range);
        setTypeArguments(typeArguments);
        setThis(isThis);
        setExpression(expression);
        setArguments(arguments);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public NodeList<Expression> getArguments() {
        return arguments;
    }

    public Expression getArgument(int i) {
        return getArguments().get(i);
    }

    public ExplicitConstructorInvocationStmt setArgument(int i, Expression argument) {
        getArguments().set(i, argument);
        return this;
    }

    public ExplicitConstructorInvocationStmt addArgument(Expression argument) {
        getArguments().add(argument);
        return this;
    }

    public Optional<Expression> getExpression() {
        return Optional.ofNullable(expression);
    }

    public boolean isThis() {
        return isThis;
    }

    public ExplicitConstructorInvocationStmt setArguments(final NodeList<Expression> arguments) {
        assertNotNull(arguments);
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
    public ExplicitConstructorInvocationStmt setExpression(final Expression expression) {
        notifyPropertyChange(ObservableProperty.EXPRESSION, this.expression, expression);
        if (this.expression != null)
            this.expression.setParentNode(null);
        this.expression = expression;
        setAsParentNodeOf(expression);
        return this;
    }

    public ExplicitConstructorInvocationStmt setThis(final boolean isThis) {
        notifyPropertyChange(ObservableProperty.THIS, this.isThis, isThis);
        this.isThis = isThis;
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
     * @return this, the ExplicitConstructorInvocationStmt
     */
    @Override
    public ExplicitConstructorInvocationStmt setTypeArguments(final NodeList<Type> typeArguments) {
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        if (this.typeArguments != null)
            this.typeArguments.setParentNode(null);
        this.typeArguments = typeArguments;
        setAsParentNodeOf(typeArguments);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getArguments(), getTypeArguments().orElse(null));
    }

    @Override
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

    public ExplicitConstructorInvocationStmt removeExpression() {
        return setExpression((Expression) null);
    }

    @Override
    public ExplicitConstructorInvocationStmt clone() {
        return (ExplicitConstructorInvocationStmt) accept(new CloneVisitor(), null);
    }

    @Override
    public ExplicitConstructorInvocationStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.explicitConstructorInvocationStmtMetaModel;
    }
}

