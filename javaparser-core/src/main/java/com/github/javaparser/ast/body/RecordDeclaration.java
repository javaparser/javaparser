/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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
import com.github.javaparser.ast.nodeTypes.NodeWithImplements;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeParameters;
import com.github.javaparser.ast.nodeTypes.modifiers.NodeWithFinalModifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.LocalClassDeclarationStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.RecordDeclarationMetaModel;
import com.github.javaparser.resolution.Resolvable;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;

import java.util.Optional;
import java.util.function.Consumer;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A definition of a record.<br>{@code record X(...) { ... }}
 */
public class RecordDeclaration extends TypeDeclaration<RecordDeclaration> implements NodeWithImplements<RecordDeclaration>, NodeWithTypeParameters<RecordDeclaration>, NodeWithFinalModifier<RecordDeclaration>, Resolvable<ResolvedReferenceTypeDeclaration> {

    private NodeList<TypeParameter> typeParameters;

    private NodeList<ClassOrInterfaceType> implementedTypes;

    public RecordDeclaration() {
        this(null, new NodeList<>(), new NodeList<>(), new SimpleName(), new NodeList<>(), new NodeList<>(), new NodeList<>());
    }

    public RecordDeclaration(final NodeList<Modifier> modifiers, final String name) {
        this(null, modifiers, new NodeList<>(), new SimpleName(name), new NodeList<>(), new NodeList<>(), new NodeList<>());
    }

    @AllFieldsConstructor
    public RecordDeclaration(final NodeList<Modifier> modifiers, final NodeList<AnnotationExpr> annotations, final SimpleName name, final NodeList<TypeParameter> typeParameters, final NodeList<ClassOrInterfaceType> implementedTypes, final NodeList<BodyDeclaration<?>> members) {
        this(null, modifiers, annotations, name, typeParameters, implementedTypes, members);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public RecordDeclaration(TokenRange tokenRange, NodeList<Modifier> modifiers, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<TypeParameter> typeParameters, NodeList<ClassOrInterfaceType> implementedTypes, NodeList<BodyDeclaration<?>> members) {
        super(tokenRange, modifiers, annotations, name, members);
        setTypeParameters(typeParameters);
        setImplementedTypes(implementedTypes);
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
    public NodeList<ClassOrInterfaceType> getImplementedTypes() {
        return implementedTypes;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<TypeParameter> getTypeParameters() {
        return typeParameters;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordDeclaration setImplementedTypes(final NodeList<ClassOrInterfaceType> implementedTypes) {
        assertNotNull(implementedTypes);
        if (implementedTypes == this.implementedTypes) {
            return (RecordDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.IMPLEMENTED_TYPES, this.implementedTypes, implementedTypes);
        if (this.implementedTypes != null)
            this.implementedTypes.setParentNode(null);
        this.implementedTypes = implementedTypes;
        setAsParentNodeOf(implementedTypes);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public RecordDeclaration setTypeParameters(final NodeList<TypeParameter> typeParameters) {
        assertNotNull(typeParameters);
        if (typeParameters == this.typeParameters) {
            return (RecordDeclaration) this;
        }
        notifyPropertyChange(ObservableProperty.TYPE_PARAMETERS, this.typeParameters, typeParameters);
        if (this.typeParameters != null)
            this.typeParameters.setParentNode(null);
        this.typeParameters = typeParameters;
        setAsParentNodeOf(typeParameters);
        return this;
    }

    // TODO document and remove duplication between here and com.github.javaparser.ast.body.ClassOrInterfaceDeclaration
    /**
     * @return is this class's parent a LocalClassDeclarationStmt ?
     */
    public boolean isLocalClassDeclaration() {
        return getParentNode().map(p -> p instanceof LocalClassDeclarationStmt).orElse(false);
    }

    // TODO document and remove duplication between here and com.github.javaparser.ast.body.ClassOrInterfaceDeclaration
    @Override
    public Optional<String> getFullyQualifiedName() {
        if (isLocalClassDeclaration()) {
            return Optional.empty();
        }
        return super.getFullyQualifiedName();
    }

    @Override
    public ResolvedReferenceTypeDeclaration resolve() {
        return getSymbolResolver().resolveDeclaration(this, ResolvedReferenceTypeDeclaration.class);
    }

    @Override
    public boolean isRecordDeclaration() {
        return true;
    }

    @Override
    public RecordDeclaration asRecordDeclaration() {
        return this;
    }

    @Override
    public Optional<RecordDeclaration> toRecordDeclaration() {
        return Optional.of(this);
    }

    public void ifRecordDeclaration(Consumer<RecordDeclaration> action) {
        action.accept(this);
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < implementedTypes.size(); i++) {
            if (implementedTypes.get(i) == node) {
                implementedTypes.remove(i);
                return true;
            }
        }
        for (int i = 0; i < typeParameters.size(); i++) {
            if (typeParameters.get(i) == node) {
                typeParameters.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < implementedTypes.size(); i++) {
            if (implementedTypes.get(i) == node) {
                implementedTypes.set(i, (ClassOrInterfaceType) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < typeParameters.size(); i++) {
            if (typeParameters.get(i) == node) {
                typeParameters.set(i, (TypeParameter) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Override
    public RecordDeclaration clone() {
        return (RecordDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    public RecordDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.recordDeclarationMetaModel;
    }
}
