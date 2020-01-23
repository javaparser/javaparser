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
package org.javaparser.ast.body;

import org.javaparser.ast.AllFieldsConstructor;
import org.javaparser.ast.Node;
import org.javaparser.ast.NodeList;
import org.javaparser.ast.expr.AnnotationExpr;
import org.javaparser.ast.nodeTypes.NodeWithAnnotations;
import org.javaparser.ast.observer.ObservableProperty;
import static org.javaparser.utils.Utils.assertNotNull;
import org.javaparser.ast.visitor.CloneVisitor;
import org.javaparser.metamodel.BodyDeclarationMetaModel;
import org.javaparser.metamodel.JavaParserMetaModel;
import org.javaparser.TokenRange;
import org.javaparser.ast.Generated;
import java.util.function.Consumer;
import static org.javaparser.utils.CodeGenerationUtils.f;
import java.util.Optional;

/**
 * Any declaration that can appear between the { and } of a class, interface, or enum.
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
    @Generated("org.javaparser.generator.core.node.MainConstructorGenerator")
    public BodyDeclaration(TokenRange tokenRange, NodeList<AnnotationExpr> annotations) {
        super(tokenRange);
        setAnnotations(annotations);
        customInitialization();
    }

    protected BodyDeclaration(TokenRange range) {
        this(range, new NodeList<>());
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    @Generated("org.javaparser.generator.core.node.PropertyGenerator")
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
    @Generated("org.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.CloneGenerator")
    public BodyDeclaration<?> clone() {
        return (BodyDeclaration<?>) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("org.javaparser.generator.core.node.GetMetaModelGenerator")
    public BodyDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.bodyDeclarationMetaModel;
    }

    @Override
    @Generated("org.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < annotations.size(); i++) {
            if (annotations.get(i) == node) {
                annotations.set(i, (AnnotationExpr) replacementNode);
                return true;
            }
        }
        return super.replace(node, replacementNode);
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAnnotationDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public AnnotationDeclaration asAnnotationDeclaration() {
        throw new IllegalStateException(f("%s is not an AnnotationDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAnnotationMemberDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public AnnotationMemberDeclaration asAnnotationMemberDeclaration() {
        throw new IllegalStateException(f("%s is not an AnnotationMemberDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isCallableDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public CallableDeclaration asCallableDeclaration() {
        throw new IllegalStateException(f("%s is not an CallableDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isClassOrInterfaceDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ClassOrInterfaceDeclaration asClassOrInterfaceDeclaration() {
        throw new IllegalStateException(f("%s is not an ClassOrInterfaceDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isConstructorDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public ConstructorDeclaration asConstructorDeclaration() {
        throw new IllegalStateException(f("%s is not an ConstructorDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnumConstantDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public EnumConstantDeclaration asEnumConstantDeclaration() {
        throw new IllegalStateException(f("%s is not an EnumConstantDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnumDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public EnumDeclaration asEnumDeclaration() {
        throw new IllegalStateException(f("%s is not an EnumDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isFieldDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public FieldDeclaration asFieldDeclaration() {
        throw new IllegalStateException(f("%s is not an FieldDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isInitializerDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public InitializerDeclaration asInitializerDeclaration() {
        throw new IllegalStateException(f("%s is not an InitializerDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMethodDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public MethodDeclaration asMethodDeclaration() {
        throw new IllegalStateException(f("%s is not an MethodDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTypeDeclaration() {
        return false;
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public TypeDeclaration asTypeDeclaration() {
        throw new IllegalStateException(f("%s is not an TypeDeclaration", this));
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAnnotationDeclaration(Consumer<AnnotationDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAnnotationMemberDeclaration(Consumer<AnnotationMemberDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCallableDeclaration(Consumer<CallableDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifClassOrInterfaceDeclaration(Consumer<ClassOrInterfaceDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifConstructorDeclaration(Consumer<ConstructorDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnumConstantDeclaration(Consumer<EnumConstantDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnumDeclaration(Consumer<EnumDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifFieldDeclaration(Consumer<FieldDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifInitializerDeclaration(Consumer<InitializerDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMethodDeclaration(Consumer<MethodDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTypeDeclaration(Consumer<TypeDeclaration> action) {
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<AnnotationDeclaration> toAnnotationDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<AnnotationMemberDeclaration> toAnnotationMemberDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<CallableDeclaration> toCallableDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ClassOrInterfaceDeclaration> toClassOrInterfaceDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<ConstructorDeclaration> toConstructorDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnumConstantDeclaration> toEnumConstantDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<EnumDeclaration> toEnumDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<FieldDeclaration> toFieldDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<InitializerDeclaration> toInitializerDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<MethodDeclaration> toMethodDeclaration() {
        return Optional.empty();
    }

    @Generated("org.javaparser.generator.core.node.TypeCastingGenerator")
    public Optional<TypeDeclaration> toTypeDeclaration() {
        return Optional.empty();
    }
}
