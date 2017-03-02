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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.nodeTypes.NodeWithVariables;
import com.github.javaparser.ast.observer.AstObserverAdapter;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNonEmpty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.VariableDeclaratorMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * The declaration of a variable.<br/><code>int x = 14;</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarator extends Node implements NodeWithType<VariableDeclarator, Type>, NodeWithSimpleName<VariableDeclarator> {

    private SimpleName name;

    private Expression initializer;

    private Type type;

    public VariableDeclarator() {
        this(null, new SimpleName(), null);
    }

    public VariableDeclarator(Type type, String variableName) {
        this(null, type, new SimpleName(variableName), null);
    }

    public VariableDeclarator(Type type, SimpleName name) {
        this(null, type, name, null);
    }

    public VariableDeclarator(Type type, String variableName, Expression initializer) {
        this(null, type, new SimpleName(variableName), initializer);
    }

    /**
     * Defines the declaration of a variable.
     *
     * @param name The identifier for this variable. IE. The variables name.
     * @param initializer What this variable should be initialized to. An {@link com.github.javaparser.ast.expr.AssignExpr}
     * is unnecessary as the <code>=</code> operator is already added.
     */
    @AllFieldsConstructor
    public VariableDeclarator(Type type, SimpleName name, Expression initializer) {
        this(null, type, name, initializer);
    }

    public VariableDeclarator(Range range, Type type, SimpleName name, Expression initializer) {
        super(range);
        setName(name);
        setInitializer(initializer);
        setType(type);
        registerObserversForDerivedProperties();
    }

    private void registerObserversForDerivedProperties() {
        // We register an observer on the type property. When it is changed the MaximumCommonType is changes as well,
        // because it is derived from the type of the variables it contains, for this reason we notify about the change
        this.register(new AstObserverAdapter() {

            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                if (property == ObservableProperty.TYPE) {
                    VariableDeclarator vd = VariableDeclarator.this;
                    if (vd.getParentNode().isPresent() && vd.getParentNode().get() instanceof NodeWithVariables) {
                        NodeWithVariables nodeWithVariables = (NodeWithVariables) vd.getParentNode().get();
                        // We calculate the value the property will assume after the change will be completed
                        Type currentMaxCommonType = nodeWithVariables.getMaximumCommonType();
                        List<Type> types = new LinkedList<>();
                        int index = nodeWithVariables.getVariables().indexOf(vd);
                        for (int i = 0; i < nodeWithVariables.getVariables().size(); i++) {
                            if (i == index) {
                                types.add((Type) newValue);
                            } else {
                                types.add(nodeWithVariables.getVariable(i).getType());
                            }
                        }
                        Type newMaxCommonType = NodeWithVariables.calculateMaximumCommonType(types);
                        ((Node) nodeWithVariables).notifyPropertyChange(ObservableProperty.MAXIMUM_COMMON_TYPE, currentMaxCommonType, newMaxCommonType);
                    }
                }
            }
        });
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
    public VariableDeclarator setName(final SimpleName name) {
        assertNotNull(name);
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    /**
     * Sets the initializer expression
     *
     * @param initializer the initializer expression, can be null
     * @return this, the VariableDeclarator
     */
    public VariableDeclarator setInitializer(final Expression initializer) {
        notifyPropertyChange(ObservableProperty.INITIALIZER, this.initializer, initializer);
        if (this.initializer != null)
            this.initializer.setParentNode(null);
        this.initializer = initializer;
        setAsParentNodeOf(initializer);
        return this;
    }

    /**
     * Will create a {@link NameExpr} with the initializer param
     *
     * @param init the initializer expression, can be null
     * @return this, the VariableDeclarator
     */
    public VariableDeclarator setInitializer(String init) {
        return setInitializer(new NameExpr(assertNonEmpty(init)));
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public VariableDeclarator setType(final Type type) {
        assertNotNull(type);
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (initializer != null) {
            if (node == initializer) {
                removeInitializer();
                return true;
            }
        }
        return super.remove(node);
    }

    public VariableDeclarator removeInitializer() {
        return setInitializer((Expression) null);
    }

    @Override
    public VariableDeclarator clone() {
        return (VariableDeclarator) accept(new CloneVisitor(), null);
    }

    @Override
    public VariableDeclaratorMetaModel getMetaModel() {
        return JavaParserMetaModel.variableDeclaratorMetaModel;
    }
}

