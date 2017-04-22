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
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.github.javaparser.ast.nodeTypes.NodeWithMembers;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithAccessModifiers;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStaticModifier;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithStrictfpModifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.TypeDeclarationMetaModel;
import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.stream.Collectors.toList;
import javax.annotation.Generated;

/**
 * A base class for all types of type declarations.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class TypeDeclaration<T extends Node> extends BodyDeclaration<T> implements NodeWithSimpleName<T>, NodeWithJavadoc<T>, NodeWithMembers<T>, NodeWithAccessModifiers<T>, NodeWithStaticModifier<T>, NodeWithStrictfpModifier<T> {

    private SimpleName name;

    private EnumSet<Modifier> modifiers;

    private NodeList<BodyDeclaration<?>> members;

    public TypeDeclaration() {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), new SimpleName(), new NodeList<>());
    }

    public TypeDeclaration(EnumSet<Modifier> modifiers, String name) {
        this(null, modifiers, new NodeList<>(), new SimpleName(name), new NodeList<>());
    }

    @AllFieldsConstructor
    public TypeDeclaration(EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<BodyDeclaration<?>> members) {
        this(null, modifiers, annotations, name, members);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public TypeDeclaration(Range range, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<BodyDeclaration<?>> members) {
        super(range, annotations);
        setModifiers(modifiers);
        setName(name);
        setMembers(members);
        customInitialization();
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
        if (members == this.members) {
            return (T) this;
        }
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
        if (modifiers == this.modifiers) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
        return (T) this;
    }

    @SuppressWarnings("unchecked")
    @Override
    public T setName(final SimpleName name) {
        assertNotNull(name);
        if (name == this.name) {
            return (T) this;
        }
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
     * @return methods or constructors whose signature match the passed signature.
     */
    public List<CallableDeclaration> getCallablesWithSignature(CallableDeclaration.Signature signature) {
        return getMembers().stream().filter(m -> m instanceof CallableDeclaration).map(m -> ((CallableDeclaration) m)).filter(m -> m.getSignature().equals(signature)).collect(toList());
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
