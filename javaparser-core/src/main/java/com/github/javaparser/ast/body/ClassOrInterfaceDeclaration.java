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
import com.github.javaparser.ast.TypeParameter;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithExtends;
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;
import java.util.List;

import static com.github.javaparser.utils.Utils.ensureNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceDeclaration extends TypeDeclaration<ClassOrInterfaceDeclaration>
        implements NodeWithImplements<ClassOrInterfaceDeclaration>, NodeWithExtends<ClassOrInterfaceDeclaration> {

    private boolean interface_;

    private List<TypeParameter> typeParameterList;

    // Can contain more than one item if this is an interface
    private List<ClassOrInterfaceType> extendsList;

    private List<ClassOrInterfaceType> implementsList;

    public ClassOrInterfaceDeclaration() {
    }

    public ClassOrInterfaceDeclaration(final EnumSet<Modifier> modifiers, final boolean isInterface,
                                       final String name) {
        super(modifiers, name);
        setInterface_(isInterface);
    }

    public ClassOrInterfaceDeclaration(final EnumSet<Modifier> modifiers,
                                       final List<AnnotationExpr> annotations, final boolean isInterface,
                                       final String name,
                                       final List<TypeParameter> typeParameterList,
                                       final List<ClassOrInterfaceType> extendsList,
                                       final List<ClassOrInterfaceType> implementsList,
                                       final List<BodyDeclaration<?>> members) {
        super(annotations, modifiers, name, members);
        setInterface_(isInterface);
        setTypeParameterList(typeParameterList);
        setExtendsList(extendsList);
        setImplementsList(implementsList);
    }

    public ClassOrInterfaceDeclaration(Range range, final EnumSet<Modifier> modifiers,
                                       final List<AnnotationExpr> annotations, final boolean isInterface,
                                       final String name,
                                       final List<TypeParameter> typeParameterList,
                                       final List<ClassOrInterfaceType> extendsList,
                                       final List<ClassOrInterfaceType> implementsList,
                                       final List<BodyDeclaration<?>> members) {
        super(range, annotations, modifiers, name, members);
        setInterface_(isInterface);
        setTypeParameterList(typeParameterList);
        setExtendsList(extendsList);
        setImplementsList(implementsList);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public List<ClassOrInterfaceType> getExtendsList() {
        extendsList = ensureNotNull(extendsList);
        return extendsList;
    }

    @Override
    public List<ClassOrInterfaceType> getImplementsList() {
        implementsList = ensureNotNull(implementsList);
        return implementsList;
    }

    public List<TypeParameter> getTypeParameterList() {
        typeParameterList = ensureNotNull(typeParameterList);
        return typeParameterList;
    }

    public boolean isInterface() {
        return interface_;
    }

    /**
     * 
     * @param extendsList a null value is currently treated as an empty list. This behavior could change
     *            in the future, so please avoid passing null
     * @return
     */
    @Override
    public ClassOrInterfaceDeclaration setExtendsList(final List<ClassOrInterfaceType> extendsList) {
        this.extendsList = extendsList;
        setAsParentNodeOf(this.extendsList);
        return this;
    }

    /**
     * 
     * @param implementsList a null value is currently treated as an empty list. This behavior could change
     *            in the future, so please avoid passing null
     */
    @Override
    public ClassOrInterfaceDeclaration setImplementsList(final List<ClassOrInterfaceType> implementsList) {
        this.implementsList = implementsList;
        setAsParentNodeOf(this.implementsList);
        return this;
    }

    public void setInterface_(final boolean interface_) {
        this.interface_ = interface_;
    }

    /**
     *
     * @param typeParameterList a null value is currently treated as an empty list. This behavior could change
     *            in the future, so please avoid passing null
     */
    public void setTypeParameterList(final List<TypeParameter> typeParameterList) {
        this.typeParameterList = typeParameterList;
        setAsParentNodeOf(this.typeParameterList);
    }




}
