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
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;
import java.util.List;

import static com.github.javaparser.utils.Utils.ensureNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class Parameter extends Node implements NodeWithType<Parameter>, NodeWithAnnotations<Parameter>, NodeWithName<Parameter>, NodeWithModifiers<Parameter> {
    private Type type;

    private boolean isVarArgs;

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private List<AnnotationExpr> annotationsList;

    private VariableDeclaratorId id;

    public Parameter() {
    }

    public Parameter(Type type, VariableDeclaratorId id) {
        setId(id);
        setType(type);
    }

    /**
     * Creates a new {@link Parameter}.
     *
     * @param type
     *            type of the parameter
     * @param name
     *            name of the parameter
     * @return instance of {@link Parameter}
     */
    public static Parameter create(Type type, String name) {
        return new Parameter(type, new VariableDeclaratorId(name));
    }

    public Parameter(EnumSet<Modifier> modifiers, Type type, VariableDeclaratorId id) {
        setModifiers(modifiers);
        setId(id);
        setType(type);
    }

    public Parameter(final Range range, EnumSet<Modifier> modifiers, List<AnnotationExpr> annotationsList, Type type,
                     boolean isVarArgs, VariableDeclaratorId id) {
        super(range);
        setModifiers(modifiers);
        setAnnotationsList(annotationsList);
        setId(id);
        setType(type);
        setIsVarArgs(isVarArgs);
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
        this.type = type;
		setAsParentNodeOf(this.type);
        return this;
    }

    public void setIsVarArgs(boolean isVarArgs) {
        this.isVarArgs = isVarArgs;
    }
    /**
     * @return the list returned could be immutable (in that case it will be empty)
     */
    @Override
    public List<AnnotationExpr> getAnnotationsList() {
        annotationsList = ensureNotNull(annotationsList);
        return annotationsList;
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
     * @param annotationsList a null value is currently treated as an empty list. This behavior could change
     *            in the future, so please avoid passing null
     */
    @Override
    @SuppressWarnings("unchecked")
    public Parameter setAnnotationsList(List<AnnotationExpr> annotationsList) {
        this.annotationsList = annotationsList;
        setAsParentNodeOf(this.annotationsList);
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
}
