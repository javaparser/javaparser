/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2017 The JavaParser Team.
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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.TypeParameter;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Represents a declaration which is callable eg. a method or a constructor.
 */
public abstract class CallableDeclaration<T extends Node> extends BodyDeclaration<T>
        implements NodeWithJavadoc<T>, NodeWithDeclaration,
        NodeWithSimpleName<T>, NodeWithModifiers<T>, NodeWithParameters<T>,
        NodeWithThrownExceptions<T>, NodeWithTypeParameters<T> {

    protected EnumSet<Modifier> modifiers;

    protected NodeList<TypeParameter> typeParameters;

    protected SimpleName name;

    protected NodeList<Parameter> parameters;

    protected NodeList<ReferenceType> thrownExceptions;

    protected BlockStmt body;

    public CallableDeclaration(Range range, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, NodeList<TypeParameter> typeParameters, SimpleName name, NodeList<Parameter> parameters, NodeList<ReferenceType> thrownExceptions, BlockStmt body) {
        super(range, annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setName(name);
        setParameters(parameters);
        setThrownExceptions(thrownExceptions);
        setBodyInternal(body);
    }

    /**
     * Sets the body.
     * Attention: a constructors body can not be null and must be tested before calling this method!
     *
     * @param body the body, can be null
     */
    protected void setBodyInternal(final BlockStmt body) {
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
    }

    /**
     * Return the modifiers of this member declaration.
     *
     * @return modifiers
     * @see Modifier
     */
    @Override
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    protected void setModifiersInternal(final EnumSet<Modifier> modifiers) {
        assertNotNull(modifiers);
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    protected void setNameInternal(final SimpleName name) {
        assertNotNull(name);
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
    }

    @Override
    public NodeList<Parameter> getParameters() {
        return parameters;
    }

    protected void setParametersInternal(final NodeList<Parameter> parameters) {
        assertNotNull(parameters);
        notifyPropertyChange(ObservableProperty.PARAMETERS, this.parameters, parameters);
        if (this.parameters != null)
            this.parameters.setParentNode(null);
        this.parameters = parameters;
        setAsParentNodeOf(parameters);
    }

    @Override
    public NodeList<ReferenceType> getThrownExceptions() {
        return thrownExceptions;
    }

    protected void setThrownExceptionsInternal(final NodeList<ReferenceType> thrownExceptions) {
        assertNotNull(thrownExceptions);
        notifyPropertyChange(ObservableProperty.THROWN_EXCEPTIONS, this.thrownExceptions, thrownExceptions);
        if (this.thrownExceptions != null)
            this.thrownExceptions.setParentNode(null);
        this.thrownExceptions = thrownExceptions;
        setAsParentNodeOf(thrownExceptions);
    }

    @Override
    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    protected void setTypeParametersInternal(final NodeList<TypeParameter> typeParameters) {
        assertNotNull(typeParameters);
        notifyPropertyChange(ObservableProperty.TYPE_PARAMETERS, this.typeParameters, typeParameters);
        if (this.typeParameters != null)
            this.typeParameters.setParentNode(null);
        this.typeParameters = typeParameters;
        setAsParentNodeOf(typeParameters);
    }

    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows) {
        return getDeclarationAsString(includingModifiers, includingThrows, true);
    }

    @Override
    public String getDeclarationAsString() {
        return getDeclarationAsString(true, true, true);
    }

    protected String appendThrowsIfRequested(boolean includingThrows) {
        StringBuilder sb = new StringBuilder();
        if (includingThrows) {
            boolean firstThrow = true;
            for (ReferenceType thr : getThrownExceptions()) {
                if (firstThrow) {
                    firstThrow = false;
                    sb.append(" throws ");
                } else {
                    sb.append(", ");
                }
                sb.append(thr.toString(prettyPrinterNoCommentsConfiguration));
            }
        }
        return sb.toString();
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getParameters(), getThrownExceptions(), getTypeParameters(), getAnnotations());
    }

}
