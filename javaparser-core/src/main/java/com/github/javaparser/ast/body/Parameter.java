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
package com.github.javaparser.ast.body;

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
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.TokenRange;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedParameterDeclaration;
import com.github.javaparser.ast.Generated;

/**
 * The parameters to a method or lambda. Lambda parameters may have inferred types, in that case "type" is UnknownType.
 * <br>Note that <a href="https://en.wikipedia.org/wiki/Parameter_(computer_programming)#Parameters_and_arguments">parameters
 * are different from arguments.</a> <br>"String x" and "float y" are the parameters in {@code int abc(String x, float
 * y) {...}}
 *
 * <br>All annotations preceding the type will be set on this object, not on the type.
 * JavaParser doesn't know if it they are applicable to the parameter or the type.
 *
 * @author Julio Vilmar Gesser
 */
public class Parameter extends Node implements NodeWithType<Parameter, Type>, NodeWithAnnotations<Parameter>, NodeWithSimpleName<Parameter>, NodeWithFinalModifier<Parameter>, Resolvable<ResolvedParameterDeclaration> {

    private Type type;

    private boolean isVarArgs;

    private NodeList<AnnotationExpr> varArgsAnnotations;

    private NodeList<Modifier> modifiers;

    private NodeList<AnnotationExpr> annotations;

    private SimpleName name;

    public Parameter() {
        this(null, new NodeList<>(), new NodeList<>(), new ClassOrInterfaceType(), false, new NodeList<>(), new SimpleName());
    }

    public Parameter(Type type, SimpleName name) {
        this(null, new NodeList<>(), new NodeList<>(), type, false, new NodeList<>(), name);
    }

    /**
     * Creates a new {@link Parameter}.
     *
     * @param type type of the parameter
     * @param name name of the parameter
     */
    public Parameter(Type type, String name) {
        this(null, new NodeList<>(), new NodeList<>(), type, false, new NodeList<>(), new SimpleName(name));
    }

    public Parameter(NodeList<Modifier> modifiers, Type type, SimpleName name) {
        this(null, modifiers, new NodeList<>(), type, false, new NodeList<>(), name);
    }

    @AllFieldsConstructor
    public Parameter(NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, Type type, boolean isVarArgs, NodeList<AnnotationExpr> varArgsAnnotations, SimpleName name) {
        this(null, modifiers, annotations, type, isVarArgs, varArgsAnnotations, name);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public Parameter(TokenRange tokenRange, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, Type type, boolean isVarArgs, NodeList<AnnotationExpr> varArgsAnnotations, SimpleName name) {
        super(tokenRange);
        this.setModifiers(modifiers);
        this.setAnnotations(annotations);
        this.setType(type);
        this.setVarArgs(isVarArgs);
        this.setVarArgsAnnotations(varArgsAnnotations);
        this.setName(name);
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
    public Type getType() {
        return this.type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public boolean isVarArgs() {
        return this.isVarArgs;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Parameter setType(final Type type) {
        assertNotNull(type);
        if (type == this.type) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null) {
            this.type.setParentNode(null);
        }
        this.type = type;
        this.setAsParentNodeOf(type);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Parameter setVarArgs(final boolean isVarArgs) {
        if (isVarArgs == this.isVarArgs) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.VAR_ARGS, this.isVarArgs, isVarArgs);
        this.isVarArgs = isVarArgs;
        return this;
    }

    /**
     * @return the list returned could be immutable (in that case it will be empty)
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getAnnotations() {
        return this.annotations;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return this.name;
    }

    /**
     * Return the modifiers of this parameter declaration.
     *
     * @return modifiers
     * @see Modifier
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<Modifier> getModifiers() {
        return this.modifiers;
    }

    /**
     * @param annotations a null value is currently treated as an empty list. This behavior could change in the future,
     * so please avoid passing null
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Parameter setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        if (annotations == this.annotations) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null) {
            this.annotations.setParentNode(null);
        }
        this.annotations = annotations;
        this.setAsParentNodeOf(annotations);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Parameter setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null) {
            this.name.setParentNode(null);
        }
        this.name = name;
        this.setAsParentNodeOf(name);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Parameter setModifiers(final NodeList<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        if (this.modifiers != null) {
            this.modifiers.setParentNode(null);
        }
        this.modifiers = modifiers;
        this.setAsParentNodeOf(modifiers);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < this.annotations.size(); i++) {
            if (this.annotations.get(i) == node) {
                this.annotations.remove(i);
                return true;
            }
        }
        for (int i = 0; i < this.modifiers.size(); i++) {
            if (this.modifiers.get(i) == node) {
                this.modifiers.remove(i);
                return true;
            }
        }
        for (int i = 0; i < this.varArgsAnnotations.size(); i++) {
            if (this.varArgsAnnotations.get(i) == node) {
                this.varArgsAnnotations.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getVarArgsAnnotations() {
        return this.varArgsAnnotations;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Parameter setVarArgsAnnotations(final NodeList<AnnotationExpr> varArgsAnnotations) {
        assertNotNull(varArgsAnnotations);
        if (varArgsAnnotations == this.varArgsAnnotations) {
            return this;
        }
        this.notifyPropertyChange(ObservableProperty.VAR_ARGS_ANNOTATIONS, this.varArgsAnnotations, varArgsAnnotations);
        if (this.varArgsAnnotations != null) {
            this.varArgsAnnotations.setParentNode(null);
        }
        this.varArgsAnnotations = varArgsAnnotations;
        this.setAsParentNodeOf(varArgsAnnotations);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public Parameter clone() {
        return (Parameter) this.accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ParameterMetaModel getMetaModel() {
        return JavaParserMetaModel.parameterMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < this.annotations.size(); i++) {
            if (this.annotations.get(i) == node) {
                this.annotations.set(i, (AnnotationExpr) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < this.modifiers.size(); i++) {
            if (this.modifiers.get(i) == node) {
                this.modifiers.set(i, (Modifier) replacementNode);
                return true;
            }
        }
        if (node == this.name) {
            this.setName((SimpleName) replacementNode);
            return true;
        }
        if (node == this.type) {
            this.setType((Type) replacementNode);
            return true;
        }
        for (int i = 0; i < this.varArgsAnnotations.size(); i++) {
            if (this.varArgsAnnotations.get(i) == node) {
                this.varArgsAnnotations.set(i, (AnnotationExpr) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public ResolvedParameterDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedParameterDeclaration.class);
    }
}
