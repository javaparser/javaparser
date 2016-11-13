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
import com.github.javaparser.ast.expr.AnnotationExpr;
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
public final class EnumDeclaration extends TypeDeclaration<EnumDeclaration>
        implements NodeWithImplements<EnumDeclaration> {

    private List<ClassOrInterfaceType> implementsList;

    private List<EnumConstantDeclaration> entriesList;

    public EnumDeclaration() {
    }

    public EnumDeclaration(EnumSet<Modifier> modifiers, String name) {
        super(modifiers, name);
    }

    public EnumDeclaration(EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, String name,
                           List<ClassOrInterfaceType> implementsList, List<EnumConstantDeclaration> entriesList,
                           List<BodyDeclaration<?>> members) {
        super(annotations, modifiers, name, members);
        setImplementsList(implementsList);
        setEntriesList(entriesList);
    }

    public EnumDeclaration(Range range, EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, String name,
                           List<ClassOrInterfaceType> implementsList, List<EnumConstantDeclaration> entriesList,
                           List<BodyDeclaration<?>> members) {
        super(range, annotations, modifiers, name, members);
        setImplementsList(implementsList);
        setEntriesList(entriesList);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }


    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public List<EnumConstantDeclaration> getEntriesList() {
        entriesList = ensureNotNull(entriesList);
        return entriesList;
    }

    @Override
    public List<ClassOrInterfaceType> getImplementsList() {
        implementsList = ensureNotNull(implementsList);
        return implementsList;
    }

    public EnumDeclaration setEntriesList(List<EnumConstantDeclaration> entriesList) {
        this.entriesList = entriesList;
		setAsParentNodeOf(this.entriesList);
        return this;
    }

    @Override
    public EnumDeclaration setImplementsList(List<ClassOrInterfaceType> implementsList) {
        this.implementsList = implementsList;
		setAsParentNodeOf(this.implementsList);
        return this;
    }



    public EnumConstantDeclaration addEnumConstant(String name) {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration(name);
        getEntriesList().add(enumConstant);
        enumConstant.setParentNode(this);
        return enumConstant;
    }


}
