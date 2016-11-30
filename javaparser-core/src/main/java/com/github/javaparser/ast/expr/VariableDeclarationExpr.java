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

package com.github.javaparser.ast.expr;

import com.github.javaparser.Range;
import com.github.javaparser.ast.ArrayBracketPair;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithElementType;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithVariables;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.stream.Collectors;

import static com.github.javaparser.ast.NodeList.nodeList;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class VariableDeclarationExpr extends Expression implements
        NodeWithElementType<VariableDeclarationExpr>,
        NodeWithModifiers<VariableDeclarationExpr>,
        NodeWithAnnotations<VariableDeclarationExpr>,
        NodeWithVariables<VariableDeclarationExpr> {

    private EnumSet<Modifier> modifiers;

    private NodeList<AnnotationExpr> annotations;

    /** @deprecated will be removed in 3.0 */
    @Deprecated
    private Type elementType;

    private NodeList<VariableDeclarator> variables;

    /** @deprecated will be removed in 3.0 */
    @Deprecated
    private NodeList<ArrayBracketPair> arrayBracketPairsAfterType;

    public VariableDeclarationExpr() {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                new ClassOrInterfaceType(),
                new NodeList<>(),
                new NodeList<>());
    }

    public VariableDeclarationExpr(final Type elementType, String variableName) {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                elementType,
                nodeList(new VariableDeclarator(variableName)),
                new NodeList<>());
    }

    public VariableDeclarationExpr(final Type elementType, VariableDeclarator var) {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                elementType,
                nodeList(var),
                new NodeList<>());
    }

    public VariableDeclarationExpr(final Type elementType, String variableName, Modifier... modifiers) {
        this(null,
                Arrays.stream(modifiers).collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))),
                new NodeList<>(),
                elementType,
                nodeList(new VariableDeclarator(variableName)),
                new NodeList<>());
    }

    public VariableDeclarationExpr(final Type elementType, VariableDeclarator var, Modifier... modifiers) {
        this(null,
                Arrays.stream(modifiers).collect(Collectors.toCollection(() -> EnumSet.noneOf(Modifier.class))),
                new NodeList<>(),
                elementType,
                nodeList(var),
                new NodeList<>());
    }

    public VariableDeclarationExpr(final Type elementType, final NodeList<VariableDeclarator> variables) {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                elementType,
                variables,
                new NodeList<>());
    }

    public VariableDeclarationExpr(final EnumSet<Modifier> modifiers, final Type elementType,
                                   final NodeList<VariableDeclarator> variables) {
        this(null,
                modifiers,
                new NodeList<>(),
                elementType,
                variables,
                new NodeList<>());
    }

    public VariableDeclarationExpr(final Range range,
                                   final EnumSet<Modifier> modifiers,
                                   final NodeList<AnnotationExpr> annotations,
                                   final Type elementType,
                                   final NodeList<VariableDeclarator> variables,
                                   final NodeList<ArrayBracketPair> arrayBracketPairsAfterType) {
        super(range);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setElementType(elementType);
        setVariables(variables);
        setArrayBracketPairsAfterElementType(arrayBracketPairsAfterType);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    /**
     * Return the modifiers of this variable declaration.
     * 
     * @see Modifier
     * @return modifiers
     */
    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    /** @deprecated will be removed in 3.0 */
    @Deprecated
    @Override
    public Type getElementType() {
        return elementType;
    }

    @Override
    public NodeList<VariableDeclarator> getVariables() {
        return variables;
    }

    @Override
    public VariableDeclarationExpr setAnnotations(final NodeList<AnnotationExpr> annotations) {
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        this.annotations = assertNotNull(annotations);
        setAsParentNodeOf(this.annotations);
        return this;
    }

    @Override
    public VariableDeclarationExpr setModifiers(final EnumSet<Modifier> modifiers) {
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
        return this;
    }

    /** @deprecated will be removed in 3.0 */
    @Deprecated
    @Override
    public VariableDeclarationExpr setElementType(final Type elementType) {
        notifyPropertyChange(ObservableProperty.ELEMENT_TYPE, this.elementType, elementType);
        this.elementType = elementType;
        setAsParentNodeOf(this.elementType);
        return this;
    }

    @Override
    public VariableDeclarationExpr setVariables(final NodeList<VariableDeclarator> variables) {
        notifyPropertyChange(ObservableProperty.VARIABLES, this.variables, variables);
        this.variables = variables;
        setAsParentNodeOf(this.variables);
        return this;
    }

    /** @deprecated will be removed in 3.0 */
    @Deprecated
    public NodeList<ArrayBracketPair> getArrayBracketPairsAfterElementType() {
        return arrayBracketPairsAfterType;
    }

    /** @deprecated will be removed in 3.0 */
    @Deprecated
    @Override
    public VariableDeclarationExpr setArrayBracketPairsAfterElementType(NodeList<ArrayBracketPair> arrayBracketPairsAfterType) {
        notifyPropertyChange(ObservableProperty.ARRAY_BRACKET_PAIRS_AFTER_TYPE, this.arrayBracketPairsAfterType, arrayBracketPairsAfterType);
        this.arrayBracketPairsAfterType = assertNotNull(arrayBracketPairsAfterType);
        setAsParentNodeOf(arrayBracketPairsAfterType);
        return this;
    }
}
