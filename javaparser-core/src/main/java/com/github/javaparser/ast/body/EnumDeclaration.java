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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithConstructors;
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.EnumDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedEnumDeclaration;
import javax.annotation.Generated;
import java.util.EnumSet;
import static com.github.javaparser.utils.Utils.assertNonEmpty;
import static com.github.javaparser.utils.Utils.assertNotNull;
import java.util.function.Consumer;
import java.util.Optional;

/**
 * The declaration of an enum.<br/><code>enum X { ... }</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class EnumDeclaration extends TypeDeclaration<EnumDeclaration> implements NodeWithImplements<EnumDeclaration>, NodeWithConstructors<EnumDeclaration>, Resolvable<ResolvedEnumDeclaration> {

    private NodeList<ClassOrInterfaceType> implementedTypes;

    private NodeList<EnumConstantDeclaration> entries;

    public EnumDeclaration() {
        this(null, EnumSet.noneOf(Modifier.class), new NodeList<>(), new SimpleName(), new NodeList<>(), new NodeList<>(), new NodeList<>());
    }

    public EnumDeclaration(EnumSet<Modifier> modifiers, String name) {
        this(null, modifiers, new NodeList<>(), new SimpleName(name), new NodeList<>(), new NodeList<>(), new NodeList<>());
    }

    @AllFieldsConstructor
    public EnumDeclaration(EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<ClassOrInterfaceType> implementedTypes, NodeList<EnumConstantDeclaration> entries, NodeList<BodyDeclaration<?>> members) {
        this(null, modifiers, annotations, name, implementedTypes, entries, members);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public EnumDeclaration(TokenRange tokenRange, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<ClassOrInterfaceType> implementedTypes, NodeList<EnumConstantDeclaration> entries, NodeList<BodyDeclaration<?>> members) {
        super(tokenRange, modifiers, annotations, name, members);
        setImplementedTypes(implementedTypes);
        setEntries(entries);
        customInitialization();
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.AcceptGenerator")
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<EnumConstantDeclaration> getEntries() {
        return entries;
    }

    public EnumConstantDeclaration getEntry(int i) {
        return getEntries().get(i);
    }

    public EnumDeclaration setEntry(int i, EnumConstantDeclaration element) {
        getEntries().set(i, element);
        return this;
    }

    public EnumDeclaration addEntry(EnumConstantDeclaration element) {
        getEntries().add(element);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<ClassOrInterfaceType> getImplementedTypes() {
        return implementedTypes;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public EnumDeclaration setEntries(final NodeList<EnumConstantDeclaration> entries) {
        assertNotNull(entries);
        if (entries == this.entries) {
            return (EnumDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.ENTRIES, this.entries, entries);
        if (this.entries != null)
            this.entries.setParentNode(null);
        this.entries = entries;
        setAsParentNodeOf(entries);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public EnumDeclaration setImplementedTypes(final NodeList<ClassOrInterfaceType> implementedTypes) {
        assertNotNull(implementedTypes);
        if (implementedTypes == this.implementedTypes) {
            return (EnumDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.IMPLEMENTED_TYPES, this.implementedTypes, implementedTypes);
        if (this.implementedTypes != null)
            this.implementedTypes.setParentNode(null);
        this.implementedTypes = implementedTypes;
        setAsParentNodeOf(implementedTypes);
        return this;
    }

    public EnumConstantDeclaration addEnumConstant(String name) {
        assertNonEmpty(name);
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration(name);
        getEntries().add(enumConstant);
        return enumConstant;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < entries.size(); i++) {
            if (entries.get(i) == node) {
                entries.remove(i);
                return true;
            }
        }
        for (int i = 0; i < implementedTypes.size(); i++) {
            if (implementedTypes.get(i) == node) {
                implementedTypes.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public EnumDeclaration clone() {
        return (EnumDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public EnumDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.enumDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < entries.size(); i++) {
            if (entries.get(i) == node) {
                entries.set(i, (EnumConstantDeclaration) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < implementedTypes.size(); i++) {
            if (implementedTypes.get(i) == node) {
                implementedTypes.set(i, (ClassOrInterfaceType) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnumDeclaration() {
        return true;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EnumDeclaration asEnumDeclaration() {
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnumDeclaration(Consumer<EnumDeclaration> action) {
        action.accept(this);
    }

    @Override
    public ResolvedEnumDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedEnumDeclaration.class);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnumDeclaration> toEnumDeclaration() {
        return Optional.of(this);
    }
}
