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
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithExtends;
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;

import static com.github.javaparser.ast.NodeList.*;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceDeclaration extends TypeDeclaration<ClassOrInterfaceDeclaration> implements 
        NodeWithImplements<ClassOrInterfaceDeclaration>, 
        NodeWithExtends<ClassOrInterfaceDeclaration>,
        NodeWithTypeParameters<ClassOrInterfaceDeclaration> {

    private boolean interface_;

    private NodeList<TypeParameter> typeParameters;

    // Can contain more than one item if this is an interface
    private NodeList<ClassOrInterfaceType> extendsList;

    private NodeList<ClassOrInterfaceType> implementsList;

    public ClassOrInterfaceDeclaration() {
        this(Range.UNKNOWN, 
                EnumSet.noneOf(Modifier.class), 
                emptyNodeList(), 
                false, 
                "",
                emptyNodeList(),
                emptyNodeList(), 
                emptyNodeList(), 
                emptyNodeList()); 
    }

    public ClassOrInterfaceDeclaration(final EnumSet<Modifier> modifiers, final boolean isInterface,
                                       final String name) {
        this(Range.UNKNOWN, 
                modifiers, 
                emptyNodeList(), 
                isInterface, 
                name,
                emptyNodeList(),
                emptyNodeList(), 
                emptyNodeList(), 
                emptyNodeList());
    }

    public ClassOrInterfaceDeclaration(final EnumSet<Modifier> modifiers,
                                       final NodeList<AnnotationExpr> annotations, final boolean isInterface,
                                       final String name,
                                       final NodeList<TypeParameter> typeParameters,
                                       final NodeList<ClassOrInterfaceType> extendsList,
                                       final NodeList<ClassOrInterfaceType> implementsList,
                                       final NodeList<BodyDeclaration<?>> members) {
        this(Range.UNKNOWN, modifiers, annotations, isInterface, name, typeParameters, extendsList, implementsList, members);
    }

    public ClassOrInterfaceDeclaration(Range range, final EnumSet<Modifier> modifiers,
                                       final NodeList<AnnotationExpr> annotations, final boolean isInterface,
                                       final String name,
                                       final NodeList<TypeParameter> typeParameters,
                                       final NodeList<ClassOrInterfaceType> extendsList,
                                       final NodeList<ClassOrInterfaceType> implementsList,
                                       final NodeList<BodyDeclaration<?>> members) {
        super(range, annotations, modifiers, name, members);
        setInterface(isInterface);
        setTypeParameters(typeParameters);
        setExtends(extendsList);
        setImplements(implementsList);
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
    public NodeList<ClassOrInterfaceType> getExtends() {
        return extendsList;
    }

    @Override
    public NodeList<ClassOrInterfaceType> getImplements() {
        return implementsList;
    }

    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    public boolean isInterface() {
        return interface_;
    }

    @Override
    public ClassOrInterfaceDeclaration setExtends(final NodeList<ClassOrInterfaceType> extendsList) {
        this.extendsList = assertNotNull(extendsList);
        setAsParentNodeOf(this.extendsList);
        return this;
    }

    @Override
    public ClassOrInterfaceDeclaration setImplements(final NodeList<ClassOrInterfaceType> implementsList) {
        this.implementsList = assertNotNull(implementsList);
        setAsParentNodeOf(this.implementsList);
        return this;
    }

    public ClassOrInterfaceDeclaration setInterface(final boolean interface_) {
        this.interface_ = interface_;
        return this;
    }

    @Override
    public ClassOrInterfaceDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        this.typeParameters = assertNotNull(typeParameters);
        setAsParentNodeOf(this.typeParameters);
        return this;
    }
}
