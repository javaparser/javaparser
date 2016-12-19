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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithExtends;
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A definition of a class or interface.<br/><code>class X { ... }</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceDeclaration extends TypeDeclaration<ClassOrInterfaceDeclaration> implements
        NodeWithImplements<ClassOrInterfaceDeclaration>,
        NodeWithExtends<ClassOrInterfaceDeclaration>,
        NodeWithTypeParameters<ClassOrInterfaceDeclaration> {

    private boolean isInterface;

    private NodeList<TypeParameter> typeParameters;

    // Can contain more than one item if this is an interface
    private NodeList<ClassOrInterfaceType> extendedTypes;

    private NodeList<ClassOrInterfaceType> implementedTypes;

    public ClassOrInterfaceDeclaration() {
        this(null,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                false,
                new SimpleName(),
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>());
    }

    public ClassOrInterfaceDeclaration(final EnumSet<Modifier> modifiers, final boolean isInterface,
                                       final String name) {
        this(null,
                modifiers,
                new NodeList<>(),
                isInterface,
                new SimpleName(name),
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>());
    }

    public ClassOrInterfaceDeclaration(final EnumSet<Modifier> modifiers,
                                       final NodeList<AnnotationExpr> annotations, final boolean isInterface,
                                       final SimpleName name,
                                       final NodeList<TypeParameter> typeParameters,
                                       final NodeList<ClassOrInterfaceType> extendedTypes,
                                       final NodeList<ClassOrInterfaceType> implementedTypes,
                                       final NodeList<BodyDeclaration<?>> members) {
        this(null, modifiers, annotations, isInterface, name, typeParameters, extendedTypes, implementedTypes, members);
    }

    public ClassOrInterfaceDeclaration(Range range, final EnumSet<Modifier> modifiers,
                                       final NodeList<AnnotationExpr> annotations, final boolean isInterface,
                                       final SimpleName name,
                                       final NodeList<TypeParameter> typeParameters,
                                       final NodeList<ClassOrInterfaceType> extendedTypes,
                                       final NodeList<ClassOrInterfaceType> implementedTypes,
                                       final NodeList<BodyDeclaration<?>> members) {
        super(range, annotations, modifiers, name, members);
        setInterface(isInterface);
        setTypeParameters(typeParameters);
        setExtendedTypes(extendedTypes);
        setImplementedTypes(implementedTypes);
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
    public NodeList<ClassOrInterfaceType> getExtendedTypes() {
        return extendedTypes;
    }

    @Override
    public NodeList<ClassOrInterfaceType> getImplementedTypes() {
        return implementedTypes;
    }

    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    public boolean isInterface() {
        return isInterface;
    }

    @Override
    public ClassOrInterfaceDeclaration setExtendedTypes(final NodeList<ClassOrInterfaceType> extendsList) {
        notifyPropertyChange(ObservableProperty.EXTENDED_TYPES, this.extendedTypes, extendsList);
        this.extendedTypes = assertNotNull(extendsList);
        setAsParentNodeOf(this.extendedTypes);
        return this;
    }

    @Override
    public ClassOrInterfaceDeclaration setImplementedTypes(final NodeList<ClassOrInterfaceType> implementsList) {
        notifyPropertyChange(ObservableProperty.IMPLEMENTED_TYPES, this.implementedTypes, implementsList);
        this.implementedTypes = assertNotNull(implementsList);
        setAsParentNodeOf(this.implementedTypes);
        return this;
    }

    public ClassOrInterfaceDeclaration setInterface(final boolean interface_) {
        notifyPropertyChange(ObservableProperty.IS_INTERFACE, this.isInterface, interface_);
        this.isInterface = interface_;
        return this;
    }

    @Override
    public ClassOrInterfaceDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        notifyPropertyChange(ObservableProperty.TYPE_PARAMETERS, this.typeParameters, typeParameters);
        this.typeParameters = assertNotNull(typeParameters);
        setAsParentNodeOf(this.typeParameters);
        return this;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        List<NodeList<?>> res = new LinkedList<>(super.getNodeLists());
        res.add(typeParameters);
        res.add(extendedTypes);
        res.add(implementedTypes);
        return res;
    }
}
