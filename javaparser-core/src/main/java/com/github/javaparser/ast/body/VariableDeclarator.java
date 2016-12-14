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
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-14.html#jls-14.4">JLS</a>
 * The declaration of a variable. <code>int x = 14;</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarator extends Node implements
        NodeWithType<VariableDeclarator, Type<?>>,
        NodeWithSimpleName<VariableDeclarator> {

    private SimpleName name;

    private Expression initializer;

    private Type<?> type;

    public VariableDeclarator() {
        this(null, new SimpleName(), null);
    }

    public VariableDeclarator(Type<?> type, SimpleName name) {
        this(null, type, name, null);
    }

    public VariableDeclarator(Type<?> type, String variableName) {
        this(null, type, new SimpleName(variableName), null);
    }

    /**
     * Defines the declaration of a variable.
     *
     * @param name The identifier for this variable. IE. The variables name.
     * @param initializer What this variable should be initialized to. An {@link com.github.javaparser.ast.expr.AssignExpr}
     * is unnecessary as the <code>=</code> operator is already added.
     */
    public VariableDeclarator(Type<?> type, SimpleName name, Expression initializer) {
        this(null, type, name, initializer);
    }

    public VariableDeclarator(Type<?> type, String variableName, Expression initializer) {
        this(null, type, new SimpleName(variableName), initializer);
    }

    public VariableDeclarator(Range range, Type<?> type, SimpleName name, Expression initializer) {
        super(range);
        setName(name);
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

    public Optional<Expression> getInitializer() {
        return Optional.ofNullable(initializer);
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    @Override
    public VariableDeclarator setName(SimpleName name) {
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(name);
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
    public VariableDeclarator setInitializer(String init) {
        return setInitializer(new NameExpr(assertNotNull(init)));
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
