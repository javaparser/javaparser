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

import com.github.javaparser.TokenRange;
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
import javax.annotation.Generated;
import java.util.EnumSet;
import java.util.List;
import java.util.function.Consumer;
import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.stream.Collectors.toList;
import com.github.javaparser.ast.Node;
import java.util.Optional;

/**
 * A base class for all types of type declarations.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class TypeDeclaration<T extends TypeDeclaration<?>> extends BodyDeclaration<T> implements NodeWithSimpleName<T>, NodeWithJavadoc<T>, NodeWithMembers<T>, NodeWithAccessModifiers<T>, NodeWithStaticModifier<T>, NodeWithStrictfpModifier<T> {

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

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public TypeDeclaration(TokenRange tokenRange, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<BodyDeclaration<?>> members) {
        super(tokenRange, annotations);
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<BodyDeclaration<?>> getMembers() {
        return members;
    }

    /**
     * Return the modifiers of this type declaration.
     *
     * @return modifiers
     * @see Modifier
     */
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public EnumSet<Modifier> getModifiers() {
        return modifiers;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
    public T setModifiers(final EnumSet<Modifier> modifiers) {
        assertNotNull(modifiers);
        if (modifiers == this.modifiers) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.MODIFIERS, this.modifiers, modifiers);
        this.modifiers = modifiers;
        return (T) this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
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

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public SimpleName getName() {
        return name;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
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
     * @return methods or constructors whose signatures match the passed signature.
     */
    public List<CallableDeclaration<?>> getCallablesWithSignature(CallableDeclaration.Signature signature) {
        return getMembers().stream().filter(m -> m instanceof CallableDeclaration).map(m -> ((CallableDeclaration<?>) m)).filter(m -> m.getSignature().equals(signature)).collect(toList());
    }

    /**
     * @return is this type's parent a TypeDeclaration?
     * NOTE: many people are confused over terminology. Refer to https://docs.oracle.com/javase/tutorial/java/javaOO/nested.html .
     */
    public boolean isNestedType() {
        return getParentNode().map(p -> p instanceof TypeDeclaration).orElse(false);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public TypeDeclaration<?> clone() {
        return (TypeDeclaration<?>) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public TypeDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.typeDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < members.size(); i++) {
            if (members.get(i) == node) {
                members.set(i, (BodyDeclaration) replacementNode);
                return true;
            }
        }
        if (node == name) {
            setName((SimpleName) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTypeDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public TypeDeclaration asTypeDeclaration() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTypeDeclaration(Consumer<TypeDeclaration> action) {
        action.accept(this);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<TypeDeclaration> toTypeDeclaration() {
        return Optional.of(this);
    }
}
