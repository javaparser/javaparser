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

package com.github.javaparser.ast.body;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.nodeTypes.NodeWithVariableDeclaratorId;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarator extends Node implements
        NodeWithType<VariableDeclarator, Type<?>>,
        NodeWithVariableDeclaratorId<VariableDeclarator> {

    private VariableDeclaratorId identifier;

    private Expression initializer;

    private Type<?> type;

    public VariableDeclarator() {
        this(null, new VariableDeclaratorId(), null);
    }

    public VariableDeclarator(Type<?> type, VariableDeclaratorId identifier) {
        this(null, type, identifier, null);
    }

    public VariableDeclarator(Type<?> type, String variableName) {
        this(null, type, new VariableDeclaratorId(variableName), null);
    }

    /**
     * Defines the declaration of a variable.
     *
     * @param identifier The identifier for this variable. IE. The variables name.
     * @param initializer What this variable should be initialized to. An {@link com.github.javaparser.ast.expr.AssignExpr}
     * is unnecessary as the <code>=</code> operator is already added.
     */
    public VariableDeclarator(Type<?> type, VariableDeclaratorId identifier, Expression initializer) {
        this(null, type, identifier, initializer);
    }

    public VariableDeclarator(Type<?> type, String variableName, Expression initializer) {
        this(null, type, new VariableDeclaratorId(variableName), initializer);
    }

    public VariableDeclarator(Range range, Type<?> type, VariableDeclaratorId identifier, Expression initializer) {
        super(range);
        setIdentifier(identifier);
        setInitializer(initializer);
        setType(type);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public VariableDeclaratorId getIdentifier() {
        return identifier;
    }

    public Optional<Expression> getInitializer() {
        return Optional.ofNullable(initializer);
    }

    public VariableDeclarator setIdentifier(VariableDeclaratorId identifier) {
        notifyPropertyChange(ObservableProperty.IDENTIFIER, this.identifier, identifier);
        this.identifier = assertNotNull(identifier);
        setAsParentNodeOf(this.identifier);
        return this;
    }

    /**
     * Sets the initializer expression
     *
     * @param initializer the initializer expression, can be null
     * @return this, the VariableDeclarator
     */
    public VariableDeclarator setInitializer(Expression initializer) {
        notifyPropertyChange(ObservableProperty.INITIALIZER, this.initializer, initializer);
        this.initializer = initializer;
        setAsParentNodeOf(this.initializer);
        return this;
    }

    /**
     * Will create a {@link NameExpr} with the initializer param
     *
     * @param init the initializer expression, can be null
     * @return this, the VariableDeclarator
     */
    public VariableDeclarator setInit(String init) {
        NameExpr newInit = new NameExpr(assertNotNull(init));
        notifyPropertyChange(ObservableProperty.INITIALIZER, this.initializer, newInit);
        this.initializer = newInit;
        setAsParentNodeOf(this.initializer);
        return this;
    }

    @Override
    public Type<?> getType() {
        return type;
    }

    @Override
    public VariableDeclarator setType(Type<?> type) {
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        setAsParentNodeOf(this.type);
        return this;
    }
}
