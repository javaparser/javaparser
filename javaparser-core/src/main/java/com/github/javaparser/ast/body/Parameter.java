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
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.ParameterMetaModel;
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
public final class Parameter extends Node implements NodeWithType<Parameter, Type>, NodeWithAnnotations<Parameter>, NodeWithSimpleName<Parameter>, NodeWithFinalModifier<Parameter> {

    private Type type;

    private boolean isVarArgs;

    private NodeList<AnnotationExpr> varArgsAnnotations;

    private EnumSet<Modifier> modifiers;

    private NodeList<AnnotationExpr> annotations;

    private SimpleName name;

    public Parameter() {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), new ClassOrInterfaceType(), false, new NodeList<>(), new SimpleName());
    }

    public Parameter(Type type, SimpleName name) {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), type, false, new NodeList<>(), name);
    }

    /**
     * Creates a new {@link Parameter}.
     *
     * @param type type of the parameter
     * @param name name of the parameter
     */
    public Parameter(Type type, String name) {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), type, false, new NodeList<>(), new SimpleName(name));
    }

    public Parameter(EnumSet<Modifier> modifiers, Type type, SimpleName name) {
        this(null, modifiers, new NodeList<>(), type, false, new NodeList<>(), name);
    }

    @AllFieldsConstructor
    public Parameter(EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, Type type, boolean isVarArgs, NodeList<AnnotationExpr> varArgsAnnotations, SimpleName name) {
        this(null, modifiers, annotations, type, isVarArgs, varArgsAnnotations, name);
    }

    public Parameter(final Range range, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, Type type, boolean isVarArgs, NodeList<AnnotationExpr> varArgsAnnotations, SimpleName name) {
        super(range);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setName(name);
        setType(type);
        setVarArgs(isVarArgs);
        setVarArgsAnnotations(varArgsAnnotations);
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
    public Parameter setType(final Type type) {
        assertNotNull(type);
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    public Parameter setVarArgs(final boolean isVarArgs) {
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
    public Parameter setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null)
            this.annotations.setParentNode(null);
        this.annotations = annotations;
        setAsParentNodeOf(annotations);
        return this;
    }

    @Override
    public Parameter setName(final SimpleName name) {
        assertNotNull(name);
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    public Parameter setModifiers(final EnumSet<Modifier> modifiers) {
        assertNotNull(modifiers);
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getAnnotations(), getVarArgsAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        for (int i = 0; i < varArgsAnnotations.size(); i++) {
            if (varArgsAnnotations.get(i) == node) {
                varArgsAnnotations.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    public NodeList<AnnotationExpr> getVarArgsAnnotations() {
        return varArgsAnnotations;
    }

    public Parameter setVarArgsAnnotations(final NodeList<AnnotationExpr> varArgsAnnotations) {
        assertNotNull(varArgsAnnotations);
        notifyPropertyChange(ObservableProperty.VAR_ARGS_ANNOTATIONS, this.varArgsAnnotations, varArgsAnnotations);
        if (this.varArgsAnnotations != null)
            this.varArgsAnnotations.setParentNode(null);
        this.varArgsAnnotations = varArgsAnnotations;
        setAsParentNodeOf(varArgsAnnotations);
        return this;
    }

    @Override
    public Parameter clone() {
        return (Parameter) accept(new CloneVisitor(), null);
    }

    @Override
    public ParameterMetaModel getMetaModel() {
        return JavaParserMetaModel.parameterMetaModel;
    }
}
