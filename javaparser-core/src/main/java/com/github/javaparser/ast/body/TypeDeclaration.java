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
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.github.javaparser.ast.nodeTypes.NodeWithMembers;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.TypeDeclarationMetaModel;
import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A base class for all types of type declarations.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class TypeDeclaration<T extends Node> extends BodyDeclaration<T> implements NodeWithSimpleName<T>, NodeWithJavadoc<T>, NodeWithModifiers<T>, NodeWithMembers<T> {

    private SimpleName name;

    private EnumSet<Modifier> modifiers;

    private NodeList<BodyDeclaration<?>> members;

    public TypeDeclaration() {
        this(null, new NodeList<>(), EnumSet.noneOf(Modifier.class), new SimpleName(), new NodeList<>());
    }

    public TypeDeclaration(EnumSet<Modifier> modifiers, String name) {
        this(null, new NodeList<>(), modifiers, new SimpleName(name), new NodeList<>());
    }

    public TypeDeclaration(NodeList<AnnotationExpr> annotations, EnumSet<Modifier> modifiers, SimpleName name, NodeList<BodyDeclaration<?>> members) {
        this(null, annotations, modifiers, name, members);
    }

    public TypeDeclaration(Range range, NodeList<AnnotationExpr> annotations, EnumSet<Modifier> modifiers, SimpleName name, NodeList<BodyDeclaration<?>> members) {
        super(range, annotations);
        setName(name);
        setModifiers(modifiers);
        setMembers(members);
    }

    /**
     * Adds the given declaration to the specified type.
     *
     * @param decl member declaration
     */
    public T addMember(BodyDeclaration<?> decl) {
        NodeList<BodyDeclaration<?>> members = getMembers();
        members.add(decl);
        return (T) this;
    }

    @Override
    public NodeList<BodyDeclaration<?>> getMembers() {
        return members;
    }

    /**
     * Return the modifiers of this type declaration.
     *
     * @return modifiers
     * @see Modifier
     */
    @Override
    public final EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    @SuppressWarnings("unchecked")
    @Override
    public T setMembers(final NodeList<BodyDeclaration<?>> members) {
        assertNotNull(members);
        notifyPropertyChange(ObservableProperty.MEMBERS, this.members, members);
        if (this.members != null)
            this.members.setParentNode(null);
        this.members = members;
        setAsParentNodeOf(members);
        return (T) this;
    }

    @SuppressWarnings("unchecked")
    @Override
    public T setModifiers(final EnumSet<Modifier> modifiers) {
        assertNotNull(modifiers);
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
        return (T) this;
    }

    @SuppressWarnings("unchecked")
    @Override
    public T setName(final SimpleName name) {
        assertNotNull(name);
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return (T) this;
    }

    @Override
    public final SimpleName getName() {
        return name;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        List<NodeList<?>> res = new LinkedList<>(super.getNodeLists());
        res.add(members);
        return res;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < members.size(); i++) {
            if (members.get(i) == node) {
                members.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    /**
     * @return is this type's parent a CompilationUnit?
     */
    public boolean isTopLevelType() {
        return getParentNode().map(p -> p instanceof CompilationUnit).orElse(false);
    }

    /**
     * @return is this type's parent a TypeDeclaration?
     */
    public boolean isNestedType() {
        return getParentNode().map(p -> p instanceof TypeDeclaration).orElse(false);
    }

    @Override
    public TypeDeclaration<?> clone() {
        return (TypeDeclaration<?>) accept(new CloneVisitor(), null);
    }

    @Override
    public TypeDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.typeDeclarationMetaModel;
    }
}
