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
import com.github.javaparser.ast.ArrayBracketPair;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.utils.Pair;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;

import static com.github.javaparser.ast.type.ArrayType.wrapInArrayTypes;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class Parameter extends Node implements
        NodeWithType<Parameter, Type<?>>,
        NodeWithElementType<Parameter>,
        NodeWithAnnotations<Parameter>,
        NodeWithSimpleName<Parameter>,
        NodeWithModifiers<Parameter>,
        NodeWithVariableDeclaratorId<Parameter> {

    private Type<?> elementType;

    private boolean isVarArgs;

    private EnumSet<Modifier> modifiers;

    private NodeList<AnnotationExpr> annotations;

    private VariableDeclaratorId identifier;

    private NodeList<ArrayBracketPair> arrayBracketPairsAfterType;

    public Parameter() {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                new ClassOrInterfaceType(),
                new NodeList<>(),
                false,
                new VariableDeclaratorId());
    }

    public Parameter(Type<?> elementType, VariableDeclaratorId identifier) {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                elementType,
                new NodeList<>(),
                false,
                identifier);
    }

    /**
     * Creates a new {@link Parameter}.
     *
     * @param elementType type of the parameter
     * @param name name of the parameter
     */
    public Parameter(Type<?> elementType, String name) {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                elementType,
                new NodeList<>(),
                false,
                new VariableDeclaratorId(name));
    }

    public Parameter(EnumSet<Modifier> modifiers, Type<?> elementType, VariableDeclaratorId identifier) {
        this(null,
                modifiers,
                new NodeList<>(),
                elementType,
                new NodeList<>(),
                false,
                identifier);
    }

    public Parameter(final Range range,
                     EnumSet<Modifier> modifiers,
                     NodeList<AnnotationExpr> annotations,
                     Type<?> elementType,
                     NodeList<ArrayBracketPair> arrayBracketPairsAfterElementType,
                     boolean isVarArgs,
                     VariableDeclaratorId identifier) {
        super(range);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setIdentifier(identifier);
        setElementType(elementType);
        setVarArgs(isVarArgs);
        setArrayBracketPairsAfterElementType(assertNotNull(arrayBracketPairsAfterElementType));
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
    public Type<?> getType() {
        return wrapInArrayTypes((Type<?>) elementType.clone(),
                getArrayBracketPairsAfterElementType(),
                getIdentifier().getArrayBracketPairsAfterId());
    }

    public boolean isVarArgs() {
        return isVarArgs;
    }

    @Override
    public Parameter setType(Type<?> type) {
        Pair<Type<?>, NodeList<ArrayBracketPair>> unwrapped = ArrayType.unwrapArrayTypes(type);
        setElementType(unwrapped.a);
        setArrayBracketPairsAfterElementType(unwrapped.b);
        getIdentifier().setArrayBracketPairsAfterId(new NodeList<>());
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
    public VariableDeclaratorId getIdentifier() {
        return identifier;
    }
    
    @Override
    public SimpleName getName() {
        return getIdentifier().getName();
    }

    @Override
    public Parameter setName(SimpleName name) {
        assertNotNull(name);
        if (identifier != null) {
            identifier.setName(name);
        } else {
            VariableDeclaratorId newId = new VariableDeclaratorId(name);
            notifyPropertyChange(ObservableProperty.ID, this.identifier, newId);
            identifier = newId;
        }
        return this;
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
    public Parameter setIdentifier(VariableDeclaratorId identifier) {
        this.identifier = identifier;
        setAsParentNodeOf(this.identifier);
        return this;
    }

    @Override
    public Parameter setModifiers(EnumSet<Modifier> modifiers) {
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = assertNotNull(modifiers);
        return this;
    }

    @Override
    public Type getElementType() {
        return elementType;
    }

    @Override
    public Parameter setElementType(final Type<?> elementType) {
        notifyPropertyChange(ObservableProperty.ELEMENT_TYPE, this.elementType, elementType);
        this.elementType = assertNotNull(elementType);
        setAsParentNodeOf(this.elementType);
        return this;
    }

    @Override
    public NodeList<ArrayBracketPair> getArrayBracketPairsAfterElementType() {
        return arrayBracketPairsAfterType;
    }

    @Override
    public Parameter setArrayBracketPairsAfterElementType(NodeList<ArrayBracketPair> arrayBracketPairsAfterType) {
        notifyPropertyChange(ObservableProperty.ARRAY_BRACKET_PAIRS_AFTER_TYPE,
                this.arrayBracketPairsAfterType, arrayBracketPairsAfterType);
        this.arrayBracketPairsAfterType = assertNotNull(arrayBracketPairsAfterType);
        setAsParentNodeOf(arrayBracketPairsAfterType);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(annotations, arrayBracketPairsAfterType);
    }
}
