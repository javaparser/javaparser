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
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.type.ArrayType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.utils.Pair;

import static com.github.javaparser.ast.NodeList.*;
import static com.github.javaparser.ast.type.ArrayType.wrapInArrayTypes;
import java.util.EnumSet;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class Parameter extends Node implements
        NodeWithType<Parameter>,
        NodeWithElementType<Parameter>,
        NodeWithAnnotations<Parameter>,
        NodeWithName<Parameter>,
        NodeWithModifiers<Parameter> {

    private Type elementType;

    private boolean isVarArgs;

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private NodeList<AnnotationExpr> annotations = new NodeList<>();

    private VariableDeclaratorId id;

    private NodeList<ArrayBracketPair> arrayBracketPairsAfterType;

    public Parameter() {
        this(Range.UNKNOWN,
                EnumSet.noneOf(Modifier.class),
                emptyNodeList(),
                new ClassOrInterfaceType(),
                emptyNodeList(),
                false,
                new VariableDeclaratorId());
    }

    public Parameter(Type elementType, VariableDeclaratorId id) {
        this(Range.UNKNOWN,
                EnumSet.noneOf(Modifier.class),
                emptyNodeList(),
                elementType,
                emptyNodeList(),
                false,
                id);
    }

    /**
     * Creates a new {@link Parameter}.
     *
     * @param elementType
     *            type of the parameter
     * @param name
     *            name of the parameter
     * @return instance of {@link Parameter}
     */
    public static Parameter create(Type elementType, String name) {
        return new Parameter(Range.UNKNOWN,
                EnumSet.noneOf(Modifier.class),
                emptyNodeList(),
                elementType,
                emptyNodeList(),
                false,
                new VariableDeclaratorId(name));
    }

    public Parameter(EnumSet<Modifier> modifiers, Type elementType, VariableDeclaratorId id) {
        this(Range.UNKNOWN,
                modifiers,
                emptyNodeList(),
                elementType,
                emptyNodeList(),
                false,
                id);
    }

    public Parameter(final Range range, 
                     EnumSet<Modifier> modifiers,
                     NodeList<AnnotationExpr> annotations,
                     Type elementType,
                     NodeList<ArrayBracketPair> arrayBracketPairsAfterElementType,
                     boolean isVarArgs, 
                     VariableDeclaratorId id) {
        super(range);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setId(id);
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
    public Type getType() {
        return wrapInArrayTypes(elementType,
                getArrayBracketPairsAfterElementType(),
                getId().getArrayBracketPairsAfterId());
    }

    public boolean isVarArgs() {
        return isVarArgs;
    }

    @Override
    public Parameter setType(Type type) {
        Pair<Type, NodeList<ArrayBracketPair>> unwrapped = ArrayType.unwrapArrayTypes(type);
        setElementType(unwrapped.a);
        setArrayBracketPairsAfterElementType(unwrapped.b);
        getId().setArrayBracketPairsAfterId(emptyNodeList());
        return this;
    }

    public Parameter setVarArgs(boolean isVarArgs) {
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

    public VariableDeclaratorId getId() {
        return id;
    }

    @Override
    public String getName() {
        return getId().getName();
    }

    @SuppressWarnings("unchecked")
    @Override
    public Parameter setName(String name) {
        if (id != null)
            id.setName(name);
        else
            id = new VariableDeclaratorId(name);
        return this;
    }

    /**
     * Return the modifiers of this parameter declaration.
     *
     * @see Modifier
     * @return modifiers
     */
    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    /**
     * @param annotations a null value is currently treated as an empty list. This behavior could change
     *            in the future, so please avoid passing null
     */
    @Override
    @SuppressWarnings("unchecked")
    public Parameter setAnnotations(NodeList<AnnotationExpr> annotations) {
        this.annotations = assertNotNull(annotations);
        setAsParentNodeOf(this.annotations);
        return this;
    }

    public void setId(VariableDeclaratorId id) {
        this.id = id;
        setAsParentNodeOf(this.id);
    }

    @Override
    @SuppressWarnings("unchecked")
    public Parameter setModifiers(EnumSet<Modifier> modifiers) {
        this.modifiers = modifiers;
        return this;
    }

    @Override
    public Type getElementType() {
        return elementType;
    }

    @Override
    public Parameter setElementType(final Type elementType) {
        this.elementType = elementType;
        setAsParentNodeOf(this.elementType);
        return this;
    }

    public NodeList<ArrayBracketPair> getArrayBracketPairsAfterElementType() {
        return arrayBracketPairsAfterType;
    }

    @Override
    public Parameter setArrayBracketPairsAfterElementType(NodeList<ArrayBracketPair> arrayBracketPairsAfterType) {
        this.arrayBracketPairsAfterType = assertNotNull(arrayBracketPairsAfterType);
        setAsParentNodeOf(arrayBracketPairsAfterType);
        return this;
    }
}
