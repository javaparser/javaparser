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
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.NonEmptyProperty;
import com.github.javaparser.metamodel.OptionalProperty;
import com.github.javaparser.metamodel.VariableDeclaratorMetaModel;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNonEmpty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.TokenRange;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.ast.Generated;

/**
 * The declaration of a variable.<br/>In <code>int x = 14, y = 3;</code> "int x = 14"  and "int y = 3"  are
 * VariableDeclarators.
 * <p/>The type is on all of the variable declarators because, thanks to array brackets, each variable can have a different type.
 *
 * @author Julio Vilmar Gesser
 */
public class VariableDeclarator extends Node implements NodeWithType<VariableDeclarator, Type>, NodeWithSimpleName<VariableDeclarator>, Resolvable<ResolvedValueDeclaration> {

    private SimpleName name;

    @OptionalProperty
    @NonEmptyProperty
    private Expression initializer;

    private Type type;

    public VariableDeclarator() {
        this(null, new ClassOrInterfaceType(), new SimpleName(), null);
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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public VariableDeclarator(TokenRange tokenRange, Type type, SimpleName name, Expression initializer) {
        super(tokenRange);
        setType(type);
        setName(name);
        setInitializer(initializer);
        customInitialization();
    }

    @Override
    protected void customInitialization() {
        // We register an observer on the type property. When it is changed the MaximumCommonType is changes as well,
        // because it is derived from the type of the variables it contains, for this reason we notify about the change
        register(new AstObserverAdapter() {

            @Override
            public void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue) {
                if (property == ObservableProperty.TYPE) {
                    VariableDeclarator vd = VariableDeclarator.this;
                    if (vd.getParentNode().isPresent() && vd.getParentNode().get() instanceof NodeWithVariables) {
                        NodeWithVariables<?> nodeWithVariables = (NodeWithVariables<?>) vd.getParentNode().get();
                        // We calculate the value the property will assume after the change will be completed
                        Optional<Type> currentMaxCommonType = nodeWithVariables.getMaximumCommonType();
                        List<Type> types = new LinkedList<>();
                        int index = nodeWithVariables.getVariables().indexOf(vd);
                        for (int i = 0; i < nodeWithVariables.getVariables().size(); i++) {
                            if (i == index) {
                                types.add((Type) newValue);
                            } else {
                                types.add(nodeWithVariables.getVariable(i).getType());
                            }
                        }
                        Optional<Type> newMaxCommonType = NodeWithVariables.calculateMaximumCommonType(types);
                        ((Node) nodeWithVariables).notifyPropertyChange(ObservableProperty.MAXIMUM_COMMON_TYPE, currentMaxCommonType.orElse(null), newMaxCommonType.orElse(null));
                    }
                }
            }
        });
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
    public Optional<Expression> getInitializer() {
        return Optional.ofNullable(initializer);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public VariableDeclarator setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return (VariableDeclarator) this;
        }
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
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public VariableDeclarator setInitializer(final Expression initializer) {
        if (initializer == this.initializer) {
            return (VariableDeclarator) this;
        }
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Type getType() {
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public VariableDeclarator setType(final Type type) {
        assertNotNull(type);
        if (type == this.type) {
            return (VariableDeclarator) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
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

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public VariableDeclarator removeInitializer() {
        return setInitializer((Expression) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public VariableDeclarator clone() {
        return (VariableDeclarator) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public VariableDeclaratorMetaModel getMetaModel() {
        return JavaParserMetaModel.variableDeclaratorMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (initializer != null) {
            if (node == initializer) {
                setInitializer((Expression) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((SimpleName) replacementNode);
            return true;
        }
        if (node == type) {
            setType((Type) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public ResolvedValueDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedValueDeclaration.class);
    }
}
