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

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
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
import javax.annotation.Generated;
import java.util.EnumSet;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.metamodel.ReceiverParameterMetaModel;

/**
 * The rather obscure <a href="http://blog.joda.org/2015/12/explicit-receiver-parameters.html">"receiver parameter" feature of Java</a>.
 *
 * <br/>All annotations preceding the type will be set on this object, not on the type.
 * JavaParser doesn't know if it they are applicable to the receiver parameter or the type.
 *
 * @author Julio Vilmar Gesser
 */
public final class ReceiverParameter extends Node implements NodeWithType<ReceiverParameter, Type>, NodeWithAnnotations<ReceiverParameter>, NodeWithName<ReceiverParameter> {

    private Type type;

    private NodeList<AnnotationExpr> annotations;

    private Name name;

    public ReceiverParameter() {
        this(null, new NodeList<>(), new ClassOrInterfaceType(), new Name());
    }

    public ReceiverParameter(Type type, Name name) {
        this(null, new NodeList<>(), type, name);
    }

    /**
     * Creates a new {@link ReceiverParameter}.
     *
     * @param type type of the parameter
     * @param name name of the parameter
     */
    public ReceiverParameter(Type type, String name) {
        this(null, new NodeList<>(), type, new Name(name));
    }

    @AllFieldsConstructor
    public ReceiverParameter(NodeList<AnnotationExpr> annotations, Type type, Name name) {
        this(null, annotations, type, name);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public ReceiverParameter(TokenRange tokenRange, NodeList<AnnotationExpr> annotations, Type type, Name name) {
        super(tokenRange);
        setAnnotations(annotations);
        setType(type);
        setName(name);
        customInitialization();
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
        return type;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ReceiverParameter setType(final Type type) {
        assertNotNull(type);
        if (type == this.type) {
            return (ReceiverParameter) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    /**
     * @return the list returned could be immutable (in that case it will be empty)
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    /**
     * @param annotations a null value is currently treated as an empty list. This behavior could change in the future,
     * so please avoid passing null
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ReceiverParameter setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        if (annotations == this.annotations) {
            return (ReceiverParameter) this;
        }
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null)
            this.annotations.setParentNode(null);
        this.annotations = annotations;
        setAsParentNodeOf(annotations);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public ReceiverParameter clone() {
        return (ReceiverParameter) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public ReceiverParameterMetaModel getMetaModel() {
        return JavaParserMetaModel.receiverParameterMetaModel;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Name getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public ReceiverParameter setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return (ReceiverParameter) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.set(i, (AnnotationExpr) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((Name) replacementNode);
            return true;
        }
        if (node == type) {
            setType((Type) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }
}
