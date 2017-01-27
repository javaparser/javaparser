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
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * The parameters to a method or lambda. Lambda parameters may have inferred types, in that case "type" is UnknownType.
 * <br/>Note that <a href="https://en.wikipedia.org/wiki/Parameter_(computer_programming)#Parameters_and_arguments">parameters
 * are different from arguments.</a> <br/>"String x" and "float y" are the parameters in <code>int abc(String x, float
 * y) {...}</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class Parameter extends Node implements
        NodeWithType<Parameter, Type>,
        NodeWithAnnotations<Parameter>,
        NodeWithSimpleName<Parameter>,
        NodeWithModifiers<Parameter> {

    private Type type;

    private boolean isVarArgs;

    private EnumSet<Modifier> modifiers;

    private NodeList<AnnotationExpr> annotations;

    private SimpleName name;

    public Parameter() {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                new ClassOrInterfaceType(),
                false,
                new SimpleName());
    }

    public Parameter(Type type, SimpleName name) {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                type,
                false,
                name);
    }

    /**
     * Creates a new {@link Parameter}.
     *
     * @param type type of the parameter
     * @param name name of the parameter
     */
    public Parameter(Type type, String name) {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                type,
                false,
                new SimpleName(name));
    }

    public Parameter(EnumSet<Modifier> modifiers, Type type, SimpleName name) {
        this(null,
                modifiers,
                new NodeList<>(),
                type,
                false,
                name);
    }

    @AllFieldsConstructor
    public Parameter(EnumSet<Modifier> modifiers,
                     NodeList<AnnotationExpr> annotations,
                     Type type,
                     boolean isVarArgs,
                     SimpleName name) {
        this(null, modifiers, annotations, type, isVarArgs, name);
    }

    public Parameter(final Range range,
                     EnumSet<Modifier> modifiers,
                     NodeList<AnnotationExpr> annotations,
                     Type type,
                     boolean isVarArgs,
                     SimpleName name) {
        super(range);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setName(name);
        setType(type);
        setVarArgs(isVarArgs);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    @Override
    public Type getType() {
        return type;
    }

    public boolean isVarArgs() {
        return isVarArgs;
    }

    @Override
    public Parameter setType(Type type) {
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        setAsParentNodeOf(this.type);
        return this;
    }

    public Parameter setVarArgs(boolean isVarArgs) {
        notifyPropertyChange(ObservableProperty.VAR_ARGS, this.isVarArgs, isVarArgs);
        this.isVarArgs = isVarArgs;
        return this;
    }

    /**
     * @return the list returned could be immutable (in that case it will be empty)
     */
    @Override
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    /**
     * Return the modifiers of this parameter declaration.
     *
     * @return modifiers
     * @see Modifier
     */
    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    /**
     * @param annotations a null value is currently treated as an empty list. This behavior could change in the future,
     * so please avoid passing null
     */
    @Override
    public Parameter setAnnotations(NodeList<AnnotationExpr> annotations) {
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        this.annotations = assertNotNull(annotations);
        setAsParentNodeOf(this.annotations);
        return this;
    }

    @Override
    public Parameter setName(SimpleName name) {
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    public Parameter setModifiers(EnumSet<Modifier> modifiers) {
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = assertNotNull(modifiers);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(annotations);
    }
}
