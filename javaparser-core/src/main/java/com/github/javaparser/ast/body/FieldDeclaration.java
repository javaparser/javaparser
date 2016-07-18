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

import static com.github.javaparser.Position.pos;
import static com.github.javaparser.ast.internal.Utils.ensureNotNull;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.DocumentableNode;
import com.github.javaparser.ast.NodeWithModifiers;
import com.github.javaparser.ast.TypedNode;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class FieldDeclaration extends BodyDeclaration implements DocumentableNode, TypedNode, NodeWithModifiers {

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private Type type;

    private List<VariableDeclarator> variables;

    public FieldDeclaration() {
    }

    public FieldDeclaration(EnumSet<Modifier> modifiers, Type type, VariableDeclarator variable) {
    	setModifiers(modifiers);
    	setType(type);
    	List<VariableDeclarator> aux = new ArrayList<>();
    	aux.add(variable);
    	setVariables(aux);
    }

    public FieldDeclaration(EnumSet<Modifier> modifiers, Type type, List<VariableDeclarator> variables) {
    	setModifiers(modifiers);
    	setType(type);
    	setVariables(variables);
    }

    public FieldDeclaration(EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, Type type,
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
    public FieldDeclaration(int beginLine, int beginColumn, int endLine, int endColumn, EnumSet<Modifier> modifiers,
                            List<AnnotationExpr> annotations, Type type, List<VariableDeclarator> variables) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), modifiers, annotations, type, variables);
    }
    
    public FieldDeclaration(Range range, EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, Type type,
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
    public EnumSet<Modifier> getModifiers() {
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

    public void setModifiers(EnumSet<Modifier> modifiers) {
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
    public JavadocComment getJavaDoc() {
        if(getComment() instanceof JavadocComment){
            return (JavadocComment) getComment();
        }
        return null;
    }
}
