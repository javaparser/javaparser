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

import com.github.javaparser.ast.DocumentableNode;
import com.github.javaparser.ast.TypedNode;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.ArrayList;
import java.util.List;

import static com.github.javaparser.ast.internal.Utils.*;

/**
 * @author Julio Vilmar Gesser
 */
public final class FieldDeclaration extends BodyDeclaration implements DocumentableNode, TypedNode {

    private int modifiers;

    private Type type;

    private List<VariableDeclarator> variables;

    public FieldDeclaration() {
    }

    public FieldDeclaration(int modifiers, Type type, VariableDeclarator variable) {
    	setModifiers(modifiers);
    	setType(type);
    	List<VariableDeclarator> aux = new ArrayList<VariableDeclarator>();
    	aux.add(variable);
    	setVariables(aux);
    }

    public FieldDeclaration(int modifiers, Type type, List<VariableDeclarator> variables) {
    	setModifiers(modifiers);
    	setType(type);
    	setVariables(variables);
    }

    public FieldDeclaration(int modifiers, List<AnnotationExpr> annotations, Type type, List<VariableDeclarator> variables) {
        super(annotations);
        setModifiers(modifiers);
    	setType(type);
    	setVariables(variables);
    }

    public FieldDeclaration(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers, List<AnnotationExpr> annotations, Type type, List<VariableDeclarator> variables) {
        super(beginLine, beginColumn, endLine, endColumn, annotations);
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

    public void setModifiers(int modifiers) {
        this.modifiers = modifiers;
    }

    @Override
    public void setType(Type type) {
        this.type = type;
		setAsParentNodeOf(this.type);
    }

    public void setVariables(List<VariableDeclarator> variables) {
        this.variables = variables;
		setAsParentNodeOf(this.variables);
    }

    @Override
    public void setJavaDoc(JavadocComment javadocComment) {
        this.javadocComment = javadocComment;
    }

    @Override
    public JavadocComment getJavaDoc() {
        return javadocComment;
    }

    private JavadocComment javadocComment;
}
