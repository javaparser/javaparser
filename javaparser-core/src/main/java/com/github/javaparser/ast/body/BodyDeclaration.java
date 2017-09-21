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

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.observer.ObservableProperty;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.BodyDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;
import java.util.function.Consumer;

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

    /**This constructor is used by the parser and is considered private.*/
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

    @SuppressWarnings("unchecked")
    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
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

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAnnotationDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public AnnotationDeclaration asAnnotationDeclaration() {
        return (AnnotationDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isAnnotationMemberDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public AnnotationMemberDeclaration asAnnotationMemberDeclaration() {
        return (AnnotationMemberDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isCallableDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public CallableDeclaration asCallableDeclaration() {
        return (CallableDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isClassOrInterfaceDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ClassOrInterfaceDeclaration asClassOrInterfaceDeclaration() {
        return (ClassOrInterfaceDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isConstructorDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public ConstructorDeclaration asConstructorDeclaration() {
        return (ConstructorDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnumConstantDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EnumConstantDeclaration asEnumConstantDeclaration() {
        return (EnumConstantDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isEnumDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public EnumDeclaration asEnumDeclaration() {
        return (EnumDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isFieldDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public FieldDeclaration asFieldDeclaration() {
        return (FieldDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isInitializerDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public InitializerDeclaration asInitializerDeclaration() {
        return (InitializerDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isMethodDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public MethodDeclaration asMethodDeclaration() {
        return (MethodDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public boolean isTypeDeclaration() {
        return false;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public TypeDeclaration asTypeDeclaration() {
        return (TypeDeclaration) this;
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAnnotationDeclaration(Consumer<AnnotationDeclaration> action) {
        if (isAnnotationDeclaration()) {
            action.accept(asAnnotationDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifAnnotationMemberDeclaration(Consumer<AnnotationMemberDeclaration> action) {
        if (isAnnotationMemberDeclaration()) {
            action.accept(asAnnotationMemberDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifCallableDeclaration(Consumer<CallableDeclaration> action) {
        if (isCallableDeclaration()) {
            action.accept(asCallableDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifClassOrInterfaceDeclaration(Consumer<ClassOrInterfaceDeclaration> action) {
        if (isClassOrInterfaceDeclaration()) {
            action.accept(asClassOrInterfaceDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifConstructorDeclaration(Consumer<ConstructorDeclaration> action) {
        if (isConstructorDeclaration()) {
            action.accept(asConstructorDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnumConstantDeclaration(Consumer<EnumConstantDeclaration> action) {
        if (isEnumConstantDeclaration()) {
            action.accept(asEnumConstantDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifEnumDeclaration(Consumer<EnumDeclaration> action) {
        if (isEnumDeclaration()) {
            action.accept(asEnumDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifFieldDeclaration(Consumer<FieldDeclaration> action) {
        if (isFieldDeclaration()) {
            action.accept(asFieldDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifInitializerDeclaration(Consumer<InitializerDeclaration> action) {
        if (isInitializerDeclaration()) {
            action.accept(asInitializerDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifMethodDeclaration(Consumer<MethodDeclaration> action) {
        if (isMethodDeclaration()) {
            action.accept(asMethodDeclaration());
        }
    }

    @Generated("com.github.javaparser.generator.core.node.TypeCastingGenerator")
    public void ifTypeDeclaration(Consumer<TypeDeclaration> action) {
        if (isTypeDeclaration()) {
            action.accept(asTypeDeclaration());
        }
    }
}
