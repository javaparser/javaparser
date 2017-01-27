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
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.*;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A method declaration. "public int abc() {return 1;}" in this example: <code>class X { public int abc() {return 1;}
 * }</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class MethodDeclaration extends BodyDeclaration<MethodDeclaration> implements
        NodeWithJavadoc<MethodDeclaration>,
        NodeWithDeclaration,
        NodeWithSimpleName<MethodDeclaration>,
        NodeWithType<MethodDeclaration, Type>,
        NodeWithModifiers<MethodDeclaration>,
        NodeWithParameters<MethodDeclaration>,
        NodeWithThrownExceptions<MethodDeclaration>,
        NodeWithOptionalBlockStmt<MethodDeclaration>,
        NodeWithTypeParameters<MethodDeclaration> {

    private EnumSet<Modifier> modifiers;

    private NodeList<TypeParameter> typeParameters;

    private SimpleName name;

    private NodeList<Parameter> parameters;

    private NodeList<ReferenceType> thrownExceptions;

    private BlockStmt body;

    private boolean isDefault;

    private Type type;

    public MethodDeclaration() {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                new NodeList<>(),
                new ClassOrInterfaceType(),
                new SimpleName(),
                false,
                new NodeList<>(),
                new NodeList<>(),
                new BlockStmt());
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final Type type, final String name) {
        this(null,
                modifiers,
                new NodeList<>(),
                new NodeList<>(),
                type,
                new SimpleName(name),
                false,
                new NodeList<>(),
                new NodeList<>(),
                new BlockStmt());
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final String name, final Type type,
                             final NodeList<Parameter> parameters) {
        this(null,
                modifiers,
                new NodeList<>(),
                new NodeList<>(),
                type,
                new SimpleName(name),
                false,
                parameters,
                new NodeList<>(),
                new BlockStmt());
    }

    @AllFieldsConstructor
    public MethodDeclaration(final EnumSet<Modifier> modifiers,
                             final NodeList<AnnotationExpr> annotations,
                             final NodeList<TypeParameter> typeParameters,
                             final Type type,
                             final SimpleName name,
                             final boolean isDefault,
                             final NodeList<Parameter> parameters,
                             final NodeList<ReferenceType> thrownExceptions,
                             final BlockStmt body) {
        this(null,
                modifiers,
                annotations,
                typeParameters,
                type,
                name,
                isDefault,
                parameters,
                thrownExceptions,
                body);
    }

    public MethodDeclaration(Range range,
                             final EnumSet<Modifier> modifiers,
                             final NodeList<AnnotationExpr> annotations,
                             final NodeList<TypeParameter> typeParameters,
                             final Type type,
                             final SimpleName name,
                             final boolean isDefault,
                             final NodeList<Parameter> parameters,
                             final NodeList<ReferenceType> thrownExceptions,
                             final BlockStmt body) {
        super(range, annotations);
        setModifiers(modifiers);
        setTypeParameters(typeParameters);
        setType(type);
        setName(name);
        setParameters(parameters);
        setThrownExceptions(thrownExceptions);
        setBody(body);
        setDefault(isDefault);
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
    public Optional<BlockStmt> getBody() {
        return Optional.ofNullable(body);
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

    @Override
    public SimpleName getName() {
        return name;
    }

    @Override
    public NodeList<Parameter> getParameters() {
        return parameters;
    }

    @Override
    public NodeList<ReferenceType> getThrownExceptions() {
        return thrownExceptions;
    }

    @Override
    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    /**
     * Sets the body
     *
     * @param body the body, can be null
     * @return this, the MethodDeclaration
     */
    @Override
    public MethodDeclaration setBody(final BlockStmt body) {
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        this.body = body;
        setAsParentNodeOf(this.body);
        return this;
    }

    @Override
    public MethodDeclaration setModifiers(final EnumSet<Modifier> modifiers) {
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = assertNotNull(modifiers);
        return this;
    }

    @Override
    public MethodDeclaration setName(final SimpleName name) {
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(this.name);
        return this;
    }

    @Override
    public MethodDeclaration setParameters(final NodeList<Parameter> parameters) {
        notifyPropertyChange(ObservableProperty.PARAMETERS, this.parameters, parameters);
        this.parameters = assertNotNull(parameters);
        setAsParentNodeOf(this.parameters);
        return this;
    }

    @Override
    public MethodDeclaration setThrownExceptions(final NodeList<ReferenceType> thrownExceptions) {
        notifyPropertyChange(ObservableProperty.THROWN_TYPES, this.thrownExceptions, thrownExceptions);
        this.thrownExceptions = assertNotNull(thrownExceptions);
        setAsParentNodeOf(this.thrownExceptions);
        return this;
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public MethodDeclaration setType(Type type) {
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        this.type = type;
        setAsParentNodeOf(this.type);
        return this;
    }

    @Override
    public MethodDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        notifyPropertyChange(ObservableProperty.TYPE_PARAMETERS, this.typeParameters, typeParameters);
        this.typeParameters = assertNotNull(typeParameters);
        setAsParentNodeOf(typeParameters);
        return this;
    }

    public boolean isDefault() {
        return isDefault;
    }

    public MethodDeclaration setDefault(boolean isDefault) {
        this.isDefault = isDefault;
        return this;
    }

    @Override
    public String getDeclarationAsString() {
        return getDeclarationAsString(true, true, true);
    }

    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows) {
        return getDeclarationAsString(includingModifiers, includingThrows, true);
    }

    /**
     * The declaration returned has this schema:
     * <p>
     * [accessSpecifier] [static] [abstract] [final] [native]
     * [synchronized] returnType methodName ([paramType [paramName]])
     * [throws exceptionsList]
     *
     * @return method declaration as String
     */
    @Override
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows,
                                         boolean includingParameterName) {
        StringBuilder sb = new StringBuilder();
        if (includingModifiers) {
            AccessSpecifier accessSpecifier = Modifier.getAccessSpecifier(getModifiers());
            sb.append(accessSpecifier.asString());
            sb.append(accessSpecifier == AccessSpecifier.DEFAULT ? "" : " ");
            if (getModifiers().contains(Modifier.STATIC)) {
                sb.append("static ");
            }
            if (getModifiers().contains(Modifier.ABSTRACT)) {
                sb.append("abstract ");
            }
            if (getModifiers().contains(Modifier.FINAL)) {
                sb.append("final ");
            }
            if (getModifiers().contains(Modifier.NATIVE)) {
                sb.append("native ");
            }
            if (getModifiers().contains(Modifier.SYNCHRONIZED)) {
                sb.append("synchronized ");
            }
        }
        // TODO verify it does not print comments connected to the type
        sb.append(getType().toString(prettyPrinterNoCommentsConfiguration));
        sb.append(" ");
        sb.append(getName());
        sb.append("(");
        boolean firstParam = true;
        for (Parameter param : getParameters()) {
            if (firstParam) {
                firstParam = false;
            } else {
                sb.append(", ");
            }
            if (includingParameterName) {
                sb.append(param.toString(prettyPrinterNoCommentsConfiguration));
            } else {
                sb.append(param.getType().toString(prettyPrinterNoCommentsConfiguration));
                if (param.isVarArgs()) {
                    sb.append("...");
                }
            }
        }
        sb.append(")");
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
        List<NodeList<?>> res = new LinkedList<>(super.getNodeLists());
        res.add(typeParameters);
        res.add(parameters);
        res.add(thrownExceptions);
        return res;
    }
}
