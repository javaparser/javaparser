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
import java.util.ArrayList;
import java.util.List;

import com.github.javaparser.ASTHelper;
import com.github.javaparser.Range;
import com.github.javaparser.ast.DocumentableNode;
import com.github.javaparser.ast.NodeWithModifiers;
import com.github.javaparser.ast.TypedNode;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.MarkerAnnotationExpr;
import com.github.javaparser.ast.expr.NormalAnnotationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class FieldDeclaration extends BodyDeclaration<FieldDeclaration>
        implements DocumentableNode<FieldDeclaration>, TypedNode<FieldDeclaration>,
        NodeWithModifiers<FieldDeclaration> {

    private int modifiers;

    private Type type;

    private List<VariableDeclarator> variables;

    public FieldDeclaration() {
    }

    public FieldDeclaration(int modifiers, Type type, VariableDeclarator variable) {
        setModifiers(modifiers);
        setType(type);
        List<VariableDeclarator> aux = new ArrayList<>();
        aux.add(variable);
        setVariables(aux);
    }

    public FieldDeclaration(int modifiers, Type type, List<VariableDeclarator> variables) {
        setModifiers(modifiers);
        setType(type);
        setVariables(variables);
    }

    public FieldDeclaration(int modifiers, List<AnnotationExpr> annotations, Type type,
                            List<VariableDeclarator> variables) {
        super(annotations);
        setModifiers(modifiers);
        setType(type);
        setVariables(variables);
    }

    /**
     * @deprecated prefer using Range objects.
     */
    @Deprecated
    public FieldDeclaration(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers,
                            List<AnnotationExpr> annotations, Type type, List<VariableDeclarator> variables) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), modifiers, annotations, type, variables);
    }

    public FieldDeclaration(Range range, int modifiers, List<AnnotationExpr> annotations, Type type,
                            List<VariableDeclarator> variables) {
        super(range, annotations);
        setModifiers(modifiers);
        setType(type);
        setVariables(variables);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    /**
     * Return the modifiers of this member declaration.
     * 
     * @see ModifierSet
     * @return modifiers
     */
    @Override
    public int getModifiers() {
        return modifiers;
    }

    @Override
    public Type getType() {
        return type;
    }

    public List<VariableDeclarator> getVariables() {
        variables = ensureNotNull(variables);
        return variables;
    }

    public FieldDeclaration setModifiers(int modifiers) {
        this.modifiers = modifiers;
        return this;
    }

    public FieldDeclaration addModifier(int modifier) {
        this.modifiers |= modifier;
        return this;
    }

    @Override
    public FieldDeclaration setType(Type type) {
        this.type = type;
        setAsParentNodeOf(this.type);
        return this;
    }

    public void setVariables(List<VariableDeclarator> variables) {
        this.variables = variables;
        setAsParentNodeOf(this.variables);
    }

    @Override
    public JavadocComment getJavaDoc() {
        if (getComment() instanceof JavadocComment) {
            return (JavadocComment) getComment();
        }
        return null;
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
    public FieldDeclaration addMarkerAnnotation(String name) {
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
    public FieldDeclaration addMarkerAnnotation(Class<? extends Annotation> clazz) {
        tryAddImportToParentCompilationUnit(clazz);
        return addMarkerAnnotation(clazz.getSimpleName());
    }

    /**
     * Annotates this with a single member annotation
     * 
     * @param name the name of the annotation
     * @return this
     */
    public FieldDeclaration addSingleMemberAnnotation(String name, String value) {
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
    public FieldDeclaration addSingleMemberAnnotation(Class<? extends Annotation> clazz, String value) {
        tryAddImportToParentCompilationUnit(clazz);
        return addSingleMemberAnnotation(clazz.getSimpleName(), value);
    }

    /**
     * Create a getter for this field, <b>will only work if this field declares only 1 identifier and if this field is
     * already added to a ClassOrInterfaceDeclaration</b>
     * 
     * @return the {@link MethodDeclaration} created
     */
    public MethodDeclaration createGetter() {
        if (getVariables().size() != 1)
            throw new IllegalStateException("You can use this only when the field declares only 1 variable name");
        ClassOrInterfaceDeclaration parent = getParentNodeOfType(ClassOrInterfaceDeclaration.class);
        if (parent == null)
            throw new IllegalStateException(
                    "You can use this only when the field is attached to a ClassOrInterfaceDeclaration");

        String fieldName = getVariables().get(0).getId().getName();
        fieldName = fieldName.toUpperCase().substring(0, 1) + fieldName.substring(1, fieldName.length());
        MethodDeclaration getter = parent.addMethod("get" + fieldName, ModifierSet.PUBLIC).setType(getType());
        BlockStmt blockStmt = new BlockStmt();
        getter.setBody(blockStmt);
        ReturnStmt r = new ReturnStmt(ASTHelper.createNameExpr(fieldName));
        ASTHelper.addStmt(blockStmt, r);
        return getter;
    }

    /**
     * Create a setter for this field, <b>will only work if this field declares only 1 identifier and if this field is
     * already added to a ClassOrInterfaceDeclaration</b>
     * 
     * @return the {@link MethodDeclaration} created
     */
    public MethodDeclaration createSetter() {
        if (getVariables().size() != 1)
            throw new IllegalStateException("You can use this only when the field declares only 1 variable name");
        ClassOrInterfaceDeclaration parent = getParentNodeOfType(ClassOrInterfaceDeclaration.class);
        if (parent == null)
            throw new IllegalStateException(
                    "You can use this only when the field is attached to a ClassOrInterfaceDeclaration");
        String fieldName = getVariables().get(0).getId().getName();
        fieldName = fieldName.toUpperCase().substring(0, 1) + fieldName.substring(1, fieldName.length());

        MethodDeclaration setter = parent.addMethod("set" + fieldName, ModifierSet.PUBLIC).setType(ASTHelper.VOID_TYPE);
        setter.getParameters().add(new Parameter(getType(), new VariableDeclaratorId(fieldName)));
        BlockStmt blockStmt2 = new BlockStmt();
        setter.setBody(blockStmt2);
        ASTHelper.addStmt(blockStmt2, ASTHelper.createNameExpr("this." + fieldName + " = " + fieldName + ";"));
        return setter;
    }

}
