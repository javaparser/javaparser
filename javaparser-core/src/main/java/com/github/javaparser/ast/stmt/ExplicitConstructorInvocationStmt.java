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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class ExplicitConstructorInvocationStmt extends Statement implements NodeWithTypeArguments<ExplicitConstructorInvocationStmt> {

    private NodeList<Type<?>> typeArguments;

    private boolean isThis;

    private Expression expression;

    private NodeList<Expression> arguments;

    public ExplicitConstructorInvocationStmt() {
        this(null, new NodeList<>(), true, null, new NodeList<>());
    }

    public ExplicitConstructorInvocationStmt(final boolean isThis,
                                             final Expression expression, final NodeList<Expression> arguments) {
        this(null, new NodeList<>(), isThis, expression, arguments);
    }

    public ExplicitConstructorInvocationStmt(Range range,
                                             final NodeList<Type<?>> typeArguments, final boolean isThis,
                                             final Expression expression, final NodeList<Expression> arguments) {
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

    public Optional<Expression> getExpression() {
        return Optional.ofNullable(expression);
    }

    public boolean isThis() {
        return isThis;
    }

    public ExplicitConstructorInvocationStmt setArguments(final NodeList<Expression> arguments) {
        notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        this.arguments = assertNotNull(arguments);
        setAsParentNodeOf(this.arguments);
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
        this.expression = expression;
        setAsParentNodeOf(this.expression);
        return this;
    }

    public ExplicitConstructorInvocationStmt setThis(final boolean isThis) {
        notifyPropertyChange(ObservableProperty.IS_THIS, this.isThis, isThis);
        this.isThis = isThis;
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
     * @return this, the ExplicitConstructorInvocationStmt
     */
    @Override
    public ExplicitConstructorInvocationStmt setTypeArguments(final NodeList<Type<?>> typeArguments) {
        notifyPropertyChange(ObservableProperty.TYPE_ARGUMENTS, this.typeArguments, typeArguments);
        this.typeArguments = typeArguments;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
