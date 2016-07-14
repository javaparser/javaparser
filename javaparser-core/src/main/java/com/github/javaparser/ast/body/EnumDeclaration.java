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
import com.github.javaparser.ClassUtils;
import com.github.javaparser.Range;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
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
public final class EnumDeclaration extends TypeDeclaration {

    private List<ClassOrInterfaceType> implementsList;

    private List<EnumConstantDeclaration> entries;

    public EnumDeclaration() {
    }

    public EnumDeclaration(int modifiers, String name) {
        super(modifiers, name);
    }

    public EnumDeclaration(int modifiers, List<AnnotationExpr> annotations, String name, List<ClassOrInterfaceType> implementsList, List<EnumConstantDeclaration> entries, List<BodyDeclaration> members) {
        super(annotations, modifiers, name, members);
        setImplements(implementsList);
        setEntries(entries);
    }

    /**
     * @deprecated prefer using Range objects.
     */
    @Deprecated
    public EnumDeclaration(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers, List<AnnotationExpr> annotations, String name, List<ClassOrInterfaceType> implementsList, List<EnumConstantDeclaration> entries, List<BodyDeclaration> members) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), modifiers, annotations, name, implementsList, entries, members);
    }
    
    public EnumDeclaration(Range range, int modifiers, List<AnnotationExpr> annotations, String name, List<ClassOrInterfaceType> implementsList, List<EnumConstantDeclaration> entries, List<BodyDeclaration> members) {
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

    public List<EnumConstantDeclaration> getEntries() {
        entries = ensureNotNull(entries);
        return entries;
    }

    public List<ClassOrInterfaceType> getImplements() {
        implementsList = ensureNotNull(implementsList);
        return implementsList;
    }

    public void setEntries(List<EnumConstantDeclaration> entries) {
        this.entries = entries;
		setAsParentNodeOf(this.entries);
    }

    public void setImplements(List<ClassOrInterfaceType> implementsList) {
        this.implementsList = implementsList;
		setAsParentNodeOf(this.implementsList);
    }

    /**
     * Add an implements to this enum
     * 
     * @param name the name of the type to extends from
     * @return this, the {@link EnumDeclaration}
     */
    public EnumDeclaration addImplements(String name) {
        ClassOrInterfaceType classOrInterfaceType = new ClassOrInterfaceType(name);
        getImplements().add(classOrInterfaceType);
        classOrInterfaceType.setParentNode(this);
        return this;
    }

    /**
     * Add an implements to this enum and automatically add the import
     * 
     * @param clazz the type to implements from
     * @return this, the {@link EnumDeclaration}
     */
    public EnumDeclaration addImplements(Class<?> clazz) {
        CompilationUnit parentNode = getParentNodeOfType(CompilationUnit.class);
        if (parentNode != null) {
            parentNode.addImportWithoutDuplicates(clazz);
        }
        return addImplements(clazz.getSimpleName());
    }

    public EnumConstantDeclaration addEnumConstant(String name) {
        EnumConstantDeclaration enumConstant = new EnumConstantDeclaration(name);
        getEntries().add(enumConstant);
        enumConstant.setParentNode(this);
        return enumConstant;
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
        CompilationUnit parentNode = getParentNodeOfType(CompilationUnit.class);
        if (parentNode != null) {
            parentNode.addImportWithoutDuplicates(clazz);
        }
        return addAnnotation(clazz.getSimpleName());
    }

    /**
     * Annotates this with a marker annotation
     * 
     * @param name the name of the annotation
     * @return this
     */
    public EnumDeclaration addMarkerAnnotation(String name) {
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
    public EnumDeclaration addMarkerAnnotation(Class<? extends Annotation> clazz) {
        CompilationUnit parentNode = getParentNodeOfType(CompilationUnit.class);
        if (parentNode != null) {
            parentNode.addImportWithoutDuplicates(clazz);
        }
        return addMarkerAnnotation(clazz.getSimpleName());
    }

    /**
     * Annotates this with a single member annotation
     * 
     * @param name the name of the annotation
     * @return this
     */
    public EnumDeclaration addSingleMemberAnnotation(String name, String value) {
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
    public EnumDeclaration addSingleMemberAnnotation(Class<? extends Annotation> clazz, String value) {
        CompilationUnit parentNode = getParentNodeOfType(CompilationUnit.class);
        if (parentNode != null) {
            parentNode.addImportWithoutDuplicates(clazz);
        }
        return addSingleMemberAnnotation(clazz.getSimpleName(), value);
    }

    /**
     * Add a field to this {@link EnumDeclaration} and automatically add the import of the type if needed
     * 
     * @param typeClass the type of the field
     * @param modifiers the modifiers like {@link ModifierSet#PUBLIC}
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addField(Class<?> typeClass, int modifiers, String name) {
        if (!ClassUtils.isPrimitiveOrWrapper(typeClass) && !typeClass.isArray()) {
            Node parentNode = getParentNode();
            if (parentNode != null && parentNode instanceof CompilationUnit) {
                ((CompilationUnit) parentNode).addImportWithoutDuplicates(typeClass);
            }
        }
        return addField(typeClass.getSimpleName(), modifiers, name);
    }

    /**
     * Add a field to this {@link EnumDeclaration}
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
     * Add a private field to this {@link EnumDeclaration}
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addPrivateField(Class<?> typeClass, String name) {
        return addField(typeClass, ModifierSet.PRIVATE, name);
    }

    /**
     * Add a private field to this {@link EnumDeclaration} and automatically add the import of the type if
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
     * Add a public field to this {@link EnumDeclaration}
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addPublicField(Class<?> typeClass, String name) {
        return addField(typeClass, ModifierSet.PUBLIC, name);
    }

    /**
     * Add a public field to this {@link EnumDeclaration} and automatically add the import of the type if
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
     * Add a protected field to this {@link EnumDeclaration}
     * 
     * @param type the type of the field
     * @param name the name of the field
     * @return the {@link FieldDeclaration} created
     */
    public FieldDeclaration addProtectedField(Class<?> typeClass, String name) {
        return addField(typeClass, ModifierSet.PROTECTED, name);
    }

    /**
     * Add a protected field to this {@link EnumDeclaration} and automatically add the import of the type
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
     * Adds a methods to this {@link EnumDeclaration}
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
