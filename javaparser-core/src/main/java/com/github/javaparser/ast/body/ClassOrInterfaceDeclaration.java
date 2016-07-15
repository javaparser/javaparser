/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import static com.github.javaparser.Position.pos;
import static com.github.javaparser.ast.internal.Utils.ensureNotNull;

import java.lang.annotation.Annotation;
import java.util.List;

import com.github.javaparser.ASTHelper;
import com.github.javaparser.Range;
import com.github.javaparser.ast.TypeParameter;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceDeclaration extends TypeDeclaration {

    private boolean interface_;

    private List<TypeParameter> typeParameters;

    // Can contain more than one item if this is an interface
    private List<ClassOrInterfaceType> extendsList;

    private List<ClassOrInterfaceType> implementsList;

    public ClassOrInterfaceDeclaration() {
    }

    public ClassOrInterfaceDeclaration(final int modifiers, final boolean isInterface, final String name) {
        super(modifiers, name);
        setInterface(isInterface);
    }

    public ClassOrInterfaceDeclaration(final int modifiers,
                                       final List<AnnotationExpr> annotations, final boolean isInterface,
                                       final String name,
                                       final List<TypeParameter> typeParameters,
                                       final List<ClassOrInterfaceType> extendsList,
                                       final List<ClassOrInterfaceType> implementsList,
                                       final List<BodyDeclaration> members) {
        super(annotations, modifiers, name, members);
        setInterface(isInterface);
        setTypeParameters(typeParameters);
        setExtends(extendsList);
        setImplements(implementsList);
    }

    /**
     * @deprecated prefer using Range objects.
     */
    @Deprecated
    public ClassOrInterfaceDeclaration(final int beginLine, final int beginColumn, final int endLine,
                                       final int endColumn, final int modifiers,
                                       final List<AnnotationExpr> annotations, final boolean isInterface,
                                       final String name,
                                       final List<TypeParameter> typeParameters,
                                       final List<ClassOrInterfaceType> extendsList,
                                       final List<ClassOrInterfaceType> implementsList,
                                       final List<BodyDeclaration> members) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), modifiers, annotations, isInterface, name,
                typeParameters, extendsList, implementsList, members);
    }

    public ClassOrInterfaceDeclaration(Range range, final int modifiers,
                                       final List<AnnotationExpr> annotations, final boolean isInterface,
                                       final String name,
                                       final List<TypeParameter> typeParameters,
                                       final List<ClassOrInterfaceType> extendsList,
                                       final List<ClassOrInterfaceType> implementsList,
                                       final List<BodyDeclaration> members) {
        super(range, annotations, modifiers, name, members);
        setInterface(isInterface);
        setTypeParameters(typeParameters);
        setExtends(extendsList);
        setImplements(implementsList);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public List<ClassOrInterfaceType> getExtends() {
        extendsList = ensureNotNull(extendsList);
        return extendsList;
    }

    public List<ClassOrInterfaceType> getImplements() {
        implementsList = ensureNotNull(implementsList);
        return implementsList;
    }

    public List<TypeParameter> getTypeParameters() {
        typeParameters = ensureNotNull(typeParameters);
        return typeParameters;
    }

    public boolean isInterface() {
        return interface_;
    }

    /**
     * 
     * @param extendsList a null value is currently treated as an empty list. This behavior could change
     *            in the future, so please avoid passing null
     */
    public void setExtends(final List<ClassOrInterfaceType> extendsList) {
        this.extendsList = extendsList;
        setAsParentNodeOf(this.extendsList);
    }

    /**
     * 
     * @param implementsList a null value is currently treated as an empty list. This behavior could change
     *            in the future, so please avoid passing null
     */
    public void setImplements(final List<ClassOrInterfaceType> implementsList) {
        this.implementsList = implementsList;
        setAsParentNodeOf(this.implementsList);
    }

    public void setInterface(final boolean interface_) {
        this.interface_ = interface_;
    }

    /**
     *
     * @param typeParameters a null value is currently treated as an empty list. This behavior could change
     *            in the future, so please avoid passing null
     */
    public void setTypeParameters(final List<TypeParameter> typeParameters) {
        this.typeParameters = typeParameters;
        setAsParentNodeOf(this.typeParameters);
    }

    /**
     * Add an extends to this class or interface and automatically add the import
     * 
     * @param clazz the class to extand from
     * @return this, the {@link ClassOrInterfaceDeclaration}
     */
    public ClassOrInterfaceDeclaration addExtends(Class<?> clazz) {
        tryAddImportToParentCompilationUnit(clazz);
        return addExtends(clazz.getSimpleName());
    }

    /**
     * Add an extends to this class or interface
     * 
     * @param name the name of the type to extends from
     * @return this, the {@link ClassOrInterfaceDeclaration}
     */
    public ClassOrInterfaceDeclaration addExtends(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getExtends().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode(this);
        return this;
    }

    /**
     * Add an implements to this class or interface
     * 
     * @param name the name of the type to extends from
     * @return this, the {@link ClassOrInterfaceDeclaration}
     */
    public ClassOrInterfaceDeclaration addImplements(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getImplements().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode(this);
        return this;
    }

    /**
     * Add an implements to this class or interface and automatically add the import
     * 
     * @param clazz the type to implements from
     * @return this, the {@link ClassOrInterfaceDeclaration}
     */
    public ClassOrInterfaceDeclaration addImplements(Class<?> clazz) {
        tryAddImportToParentCompilationUnit(clazz);
        return addImplements(clazz.getSimpleName());
    }

    /**
     * Annotates this
     * 
     * @param name the name of the annotation
     * @return the {@link NormalAnnotationExpr} added
     */
    public NormalAnnotationExpr addAnnotation(String name) {
        NormalAnnotationExpr normalAnnotationExpr = new NormalAnnotationExpr(
                ASTHelper.createNameExpr(name), null);
        getAnnotations().add(normalAnnotationExpr);
        normalAnnotationExpr.setParentNode(this);
        return normalAnnotationExpr;
    }

    /**
     * Annotates this and automatically add the import
     * 
     * @param clazz the class of the annotation
     * @return the {@link NormalAnnotationExpr} added
     */
    public NormalAnnotationExpr addAnnotation(Class<? extends Annotation> clazz) {
        tryAddImportToParentCompilationUnit(clazz);
        return addAnnotation(clazz.getSimpleName());
    }

    /**
     * Annotates this with a marker annotation
     * 
     * @param name the name of the annotation
     * @return this
     */
    public ClassOrInterfaceDeclaration addMarkerAnnotation(String name) {
        MarkerAnnotationExpr markerAnnotationExpr = new MarkerAnnotationExpr(
                ASTHelper.createNameExpr(name));
        getAnnotations().add(markerAnnotationExpr);
        markerAnnotationExpr.setParentNode(this);
        return this;
    }

    /**
     * Annotates this with a marker annotation and automatically add the import
     * 
     * @param clazz the class of the annotation
     * @return this
     */
    public ClassOrInterfaceDeclaration addMarkerAnnotation(Class<? extends Annotation> clazz) {
        tryAddImportToParentCompilationUnit(clazz);
        return addMarkerAnnotation(clazz.getSimpleName());
    }

    /**
     * Annotates this with a single member annotation
     * 
     * @param name the name of the annotation
     * @return this
     */
    public ClassOrInterfaceDeclaration addSingleMemberAnnotation(String name, String value) {
        SingleMemberAnnotationExpr singleMemberAnnotationExpr = new SingleMemberAnnotationExpr(
                ASTHelper.createNameExpr(name), ASTHelper.createNameExpr(value));
        getAnnotations().add(singleMemberAnnotationExpr);
        singleMemberAnnotationExpr.setParentNode(this);
        return this;
    }

    /**
     * Annotates this with a single member annotation and automatically add the import
     * 
     * @param clazz the class of the annotation
     * @return this
     */
    public ClassOrInterfaceDeclaration addSingleMemberAnnotation(Class<? extends Annotation> clazz, String value) {
        tryAddImportToParentCompilationUnit(clazz);
        return addSingleMemberAnnotation(clazz.getSimpleName(), value);
    }

    /**
     * Add a field to this {@link ClassOrInterfaceDeclaration} and automatically add the import of the type if needed
     * 
     * @param typeClass the type of the field
     * @param modifiers the modifiers like {@link ModifierSet#PUBLIC}
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addField(Class<?> typeClass, int modifiers, String name) {
        tryAddImportToParentCompilationUnit(typeClass);
        return addField(typeClass.getSimpleName(), modifiers, name);
    }

    /**
     * Add a field to this {@link ClassOrInterfaceDeclaration}
     * 
     * @param type the type of the field
     * @param modifiers the modifiers like {@link ModifierSet#PUBLIC}
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addField(String type, int modifiers, String name) {
        FieldDeclaration fieldDeclaration = new FieldDeclaration();
        fieldDeclaration.getVariables().add(new VariableDeclarator(new VariableDeclaratorId(name)));
        fieldDeclaration.setModifiers(modifiers);
        fieldDeclaration.setType(new ClassOrInterfaceType(type));
        getMembers().add(fieldDeclaration);
        fieldDeclaration.setParentNode(this);
        return fieldDeclaration;
    }

    /**
     * Add a private field to this {@link ClassOrInterfaceDeclaration}
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addPrivateField(Class<?> typeClass, String name) {
        return addField(typeClass, ModifierSet.PRIVATE, name);
    }

    /**
     * Add a private field to this {@link ClassOrInterfaceDeclaration} and automatically add the import of the type if
     * needed
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addPrivateField(String type, String name) {
        return addField(type, ModifierSet.PRIVATE, name);
    }

    /**
     * Add a public field to this {@link ClassOrInterfaceDeclaration}
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addPublicField(Class<?> typeClass, String name) {
        return addField(typeClass, ModifierSet.PUBLIC, name);
    }

    /**
     * Add a public field to this {@link ClassOrInterfaceDeclaration} and automatically add the import of the type if
     * needed
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addPublicField(String type, String name) {
        return addField(type, ModifierSet.PUBLIC, name);
    }

    /**
     * Add a protected field to this {@link ClassOrInterfaceDeclaration}
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addProtectedField(Class<?> typeClass, String name) {
        return addField(typeClass, ModifierSet.PROTECTED, name);
    }

    /**
     * Add a protected field to this {@link ClassOrInterfaceDeclaration} and automatically add the import of the type
     * if needed
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addProtectedField(String type, String name) {
        return addField(type, ModifierSet.PROTECTED, name);
    }

    /**
     * Adds a methods to this {@link ClassOrInterfaceDeclaration}
     * 
     * @param methodName the method name
     * @param modifiers the modifiers like {@link ModifierSet#PUBLIC}
     * @return the {@link MethodDeclaration} created
     */
    public MethodDeclaration addMethod(String methodName, int modifiers) {
        MethodDeclaration methodDeclaration = new MethodDeclaration();
        methodDeclaration.setName(methodName);
        methodDeclaration.setModifiers(modifiers);
        getMembers().add(methodDeclaration);
        methodDeclaration.setParentNode(this);
        return methodDeclaration;
    }
}
