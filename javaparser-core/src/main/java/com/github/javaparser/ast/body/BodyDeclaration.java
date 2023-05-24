/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
import com.github.javaparser.ast.Generated;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.BodyDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import java.util.Optional;
import java.util.function.Consumer;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Any declaration that can appear between the { and } of a class, interface, enum, or record.
 *
 * @author Julio Vilmar Gesser
 */
public abstract class BodyDeclaration<T extends BodyDeclaration<?>> extends Node implements NodeWithAnnotations<T> {

    private NodeList<AnnotationExpr> annotations;

    public BodyDeclaration() {
        this(null, new NodeList<>());
    }

    @AllFieldsConstructor
    public BodyDeclaration(NodeList<AnnotationExpr> annotations) {
        this(null, annotations);
    }

    /**
     * This constructor is used by the parser and is considered private.
     */
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public BodyDeclaration(TokenRange tokenRange, NodeList<AnnotationExpr> annotations) {
        super(tokenRange);
        setAnnotations(annotations);
        customInitialization();
    }

    protected BodyDeclaration(TokenRange range) {
        this(range, new NodeList<>());
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    @SuppressWarnings("unchecked")
    public T setAnnotations(final NodeList<AnnotationExpr> annotations) {
        assertNotNull(annotations);
        if (annotations == this.annotations) {
            return (T) this;
        }
        notifyPropertyChange(ObservableProperty.ANNOTATIONS, this.annotations, annotations);
        if (this.annotations != null)
            this.annotations.setParentNode(null);
        this.annotations = annotations;
        setAsParentNodeOf(annotations);
        return (T) this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public BodyDeclaration<?> clone() {
        return (BodyDeclaration<?>) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public BodyDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.bodyDeclarationMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null) {
            return false;
        }
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.set(i, (AnnotationExpr) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAnnotationDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public AnnotationDeclaration asAnnotationDeclaration() {
        throw new IllegalStateException(f("%s is not AnnotationDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAnnotationMemberDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public AnnotationMemberDeclaration asAnnotationMemberDeclaration() {
        throw new IllegalStateException(f("%s is not AnnotationMemberDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isCallableDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public CallableDeclaration asCallableDeclaration() {
        throw new IllegalStateException(f("%s is not CallableDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isClassOrInterfaceDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ClassOrInterfaceDeclaration asClassOrInterfaceDeclaration() {
        throw new IllegalStateException(f("%s is not ClassOrInterfaceDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isConstructorDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ConstructorDeclaration asConstructorDeclaration() {
        throw new IllegalStateException(f("%s is not ConstructorDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isCompactConstructorDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public CompactConstructorDeclaration asCompactConstructorDeclaration() {
        throw new IllegalStateException(f("%s is not CompactConstructorDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnumConstantDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EnumConstantDeclaration asEnumConstantDeclaration() {
        throw new IllegalStateException(f("%s is not EnumConstantDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnumDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EnumDeclaration asEnumDeclaration() {
        throw new IllegalStateException(f("%s is not EnumDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isFieldDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public FieldDeclaration asFieldDeclaration() {
        throw new IllegalStateException(f("%s is not FieldDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isInitializerDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public InitializerDeclaration asInitializerDeclaration() {
        throw new IllegalStateException(f("%s is not InitializerDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMethodDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public MethodDeclaration asMethodDeclaration() {
        throw new IllegalStateException(f("%s is not MethodDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTypeDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public TypeDeclaration asTypeDeclaration() {
        throw new IllegalStateException(f("%s is not TypeDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAnnotationDeclaration(Consumer<AnnotationDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAnnotationMemberDeclaration(Consumer<AnnotationMemberDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCallableDeclaration(Consumer<CallableDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifClassOrInterfaceDeclaration(Consumer<ClassOrInterfaceDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifConstructorDeclaration(Consumer<ConstructorDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnumConstantDeclaration(Consumer<EnumConstantDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnumDeclaration(Consumer<EnumDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifFieldDeclaration(Consumer<FieldDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifInitializerDeclaration(Consumer<InitializerDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMethodDeclaration(Consumer<MethodDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTypeDeclaration(Consumer<TypeDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifRecordDeclaration(Consumer<RecordDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCompactConstructorDeclaration(Consumer<CompactConstructorDeclaration> action) {
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<AnnotationDeclaration> toAnnotationDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<AnnotationMemberDeclaration> toAnnotationMemberDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CallableDeclaration> toCallableDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ClassOrInterfaceDeclaration> toClassOrInterfaceDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ConstructorDeclaration> toConstructorDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnumConstantDeclaration> toEnumConstantDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnumDeclaration> toEnumDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<FieldDeclaration> toFieldDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<InitializerDeclaration> toInitializerDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<MethodDeclaration> toMethodDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<TypeDeclaration> toTypeDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isRecordDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public RecordDeclaration asRecordDeclaration() {
        throw new IllegalStateException(f("%s is not RecordDeclaration, it is %s", this, this.getClass().getSimpleName()));
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<RecordDeclaration> toRecordDeclaration() {
        return Optional.empty();
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CompactConstructorDeclaration> toCompactConstructorDeclaration() {
        return Optional.empty();
    }
}
