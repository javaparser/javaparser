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
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.observing.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class EnumDeclaration extends TypeDeclaration<EnumDeclaration> implements 
        NodeWithImplements<EnumDeclaration> {

    private NodeList<ClassOrInterfaceType> implementsList;

    private NodeList<EnumConstantDeclaration> entries;

    public EnumDeclaration() {
        this(Range.UNKNOWN, 
                EnumSet.noneOf(Modifier.class), 
                new NodeList<>(), 
                new SimpleName(), 
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>());
    }

    public EnumDeclaration(EnumSet<Modifier> modifiers, String name) {
        this(Range.UNKNOWN,
                modifiers,
                new NodeList<>(),
                new SimpleName(name),
                new NodeList<>(),
                new NodeList<>(),
                new NodeList<>());
    }

    public EnumDeclaration(EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name,
                           NodeList<ClassOrInterfaceType> implementsList, NodeList<EnumConstantDeclaration> entries,
                           NodeList<BodyDeclaration<?>> members) {
        this(Range.UNKNOWN,
                modifiers,
                annotations,
                name,
                implementsList,
                entries,
                members);
    }

    public EnumDeclaration(Range range, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name,
                           NodeList<ClassOrInterfaceType> implementsList, NodeList<EnumConstantDeclaration> entries,
                           NodeList<BodyDeclaration<?>> members) {
        super(range, annotations, modifiers, name, members);
        setImplements(implementsList);
        setEntries(entries);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }


    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public NodeList<EnumConstantDeclaration> getEntries() {
        return entries;
    }

    public EnumConstantDeclaration getEntry(int i) {
        return getEntries().get(i);
    }

    @Override
    public NodeList<ClassOrInterfaceType> getImplements() {
        return implementsList;
    }

    public EnumDeclaration setEntries(NodeList<EnumConstantDeclaration> entries) {
        notifyPropertyChange(ObservableProperty.ENTRIES, this.entries, entries);
        this.entries = assertNotNull(entries);
		setAsParentNodeOf(this.entries);
        return this;
    }

    @Override
    public EnumDeclaration setImplements(NodeList<ClassOrInterfaceType> implementsList) {
        notifyPropertyChange(ObservableProperty.IMPLEMENTS_LIST, this.implementsList, implementsList);
        this.implementsList = assertNotNull(implementsList);
		setAsParentNodeOf(this.implementsList);
        return this;
    }

    public EnumConstantDeclaration addEnumConstant(String name) {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration(assertNotNull(name));
        getEntries().add(enumConstant);
        enumConstant.setParentNode(this);
        return enumConstant;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        List<NodeList<?>> res = new LinkedList<>(super.getNodeLists());
        res.add(implementsList);
        res.add(entries);
        return res;
    }
}
