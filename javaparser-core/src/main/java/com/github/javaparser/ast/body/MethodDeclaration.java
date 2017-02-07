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
import com.github.javaparser.ast.AccessSpecifier;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
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
import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;

/**
 * A method declaration. "public int abc() {return 1;}" in this example: <code>class X { public int abc() {return 1;}
 * }</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class MethodDeclaration extends CallableDeclaration<MethodDeclaration> implements NodeWithType<MethodDeclaration, Type>, NodeWithOptionalBlockStmt<MethodDeclaration>, NodeWithModifiers<MethodDeclaration>, NodeWithJavadoc<MethodDeclaration>, NodeWithDeclaration, NodeWithSimpleName<MethodDeclaration>, NodeWithParameters<MethodDeclaration>, NodeWithThrownExceptions<MethodDeclaration>, NodeWithTypeParameters<MethodDeclaration> {

    private boolean isDefault;

    private Type type;

    private BlockStmt body;

    public MethodDeclaration() {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), new NodeList<>(), new ClassOrInterfaceType(), new SimpleName(), false, new NodeList<>(), new NodeList<>(), new BlockStmt());
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final Type type, final String name) {
        this(null, modifiers, new NodeList<>(), new NodeList<>(), type, new SimpleName(name), false, new NodeList<>(), new NodeList<>(), new BlockStmt());
    }

    public MethodDeclaration(final EnumSet<Modifier> modifiers, final String name, final Type type, final NodeList<Parameter> parameters) {
        this(null, modifiers, new NodeList<>(), new NodeList<>(), type, new SimpleName(name), false, parameters, new NodeList<>(), new BlockStmt());
    }

    @AllFieldsConstructor
    public MethodDeclaration(final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final NodeList<TypeParameter> typeParameters, final Type type, final SimpleName name, final boolean isDefault, final NodeList<Parameter> parameters, final NodeList<ReferenceType> thrownExceptions, final BlockStmt body) {
        this(null, modifiers, annotations, typeParameters, type, name, isDefault, parameters, thrownExceptions, body);
    }

    public MethodDeclaration(Range range, final EnumSet<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final NodeList<TypeParameter> typeParameters, final Type type, final SimpleName name, final boolean isDefault, final NodeList<Parameter> parameters, final NodeList<ReferenceType> thrownExceptions, final BlockStmt body) {
        super(range, modifiers, annotations, typeParameters, name, parameters, thrownExceptions);
        setType(type);
        setDefault(isDefault);
        setBody(body);
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
     * Sets the body
     *
     * @param body the body, can be null
     * @return this, the MethodDeclaration
     */
    @Override
    public MethodDeclaration setBody(final BlockStmt body) {
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public MethodDeclaration setType(final Type type) {
        assertNotNull(type);
        notifyPropertyChange(ObservableProperty.TYPE, this.type, type);
        if (this.type != null)
            this.type.setParentNode(null);
        this.type = type;
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    public MethodDeclaration setModifiers(final EnumSet<Modifier> modifiers) {
        return super.setModifiers(modifiers);
    }

    @Override
    public MethodDeclaration setName(final SimpleName name) {
        return super.setName(name);
    }

    @Override
    public MethodDeclaration setParameters(final NodeList<Parameter> parameters) {
        return super.setParameters(parameters);
    }

    @Override
    public MethodDeclaration setThrownExceptions(final NodeList<ReferenceType> thrownExceptions) {
        return super.setThrownExceptions(thrownExceptions);
    }

    @Override
    public MethodDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        return super.setTypeParameters(typeParameters);
    }

    public boolean isDefault() {
        return isDefault;
    }

    public MethodDeclaration setDefault(final boolean isDefault) {
        notifyPropertyChange(ObservableProperty.DEFAULT, this.isDefault, isDefault);
        this.isDefault = isDefault;
        return this;
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
    public String getDeclarationAsString(boolean includingModifiers, boolean includingThrows, boolean includingParameterName) {
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
        sb.append(appendThrowsIfRequested(includingThrows));
        return sb.toString();
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getParameters(), getThrownExceptions(), getTypeParameters(), getAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (body != null) {
            if (node == body) {
                removeBody();
                return true;
            }
        }
        return super.remove(node);
    }

    public MethodDeclaration removeBody() {
        return setBody((BlockStmt) null);
    }
}

