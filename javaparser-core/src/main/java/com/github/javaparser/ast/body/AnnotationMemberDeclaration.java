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

import java.util.EnumSet;
import java.util.List;

import com.github.javaparser.Range;
import com.github.javaparser.ast.DocumentableNode;
import com.github.javaparser.ast.NamedNode;
import com.github.javaparser.ast.NodeWithModifiers;
import com.github.javaparser.ast.TypedNode;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class AnnotationMemberDeclaration extends BodyDeclaration implements DocumentableNode, NamedNode, TypedNode, NodeWithModifiers {

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private Type type;

    private String name;

    private Expression defaultValue;

    public AnnotationMemberDeclaration() {
    }

    public AnnotationMemberDeclaration(EnumSet<Modifier> modifiers, Type type, String name, Expression defaultValue) {
        setModifiers(modifiers);
        setType(type);
        setName(name);
        setDefaultValue(defaultValue);
    }

    public AnnotationMemberDeclaration(EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, Type type,
                                       String name, Expression defaultValue) {
        super(annotations);
        setModifiers(modifiers);
        setType(type);
        setName(name);
        setDefaultValue(defaultValue);
    }

    /**
     * @deprecated prefer using Range objects.
     */
    @Deprecated
    public AnnotationMemberDeclaration(int beginLine, int beginColumn, int endLine, int endColumn,
                                       EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations, Type type,
                                       String name, Expression defaultValue) {
        this(new Range(pos(beginLine, beginColumn), pos(endLine, endColumn)), modifiers, annotations, type, name, defaultValue);
    }

    public AnnotationMemberDeclaration(Range range, EnumSet<Modifier> modifiers, List<AnnotationExpr> annotations,
                                       Type type, String name, Expression defaultValue) {
        super(range, annotations);
        setModifiers(modifiers);
        setType(type);
        setName(name);
        setDefaultValue(defaultValue);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public Expression getDefaultValue() {
        return defaultValue;
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
    public String getName() {
        return name;
    }

    @Override
    public Type getType() {
        return type;
    }

    public void setDefaultValue(Expression defaultValue) {
        this.defaultValue = defaultValue;
        setAsParentNodeOf(defaultValue);
    }

    public void setModifiers(EnumSet<Modifier> modifiers) {
        this.modifiers = modifiers;
    }

    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void setType(Type type) {
        this.type = type;
        setAsParentNodeOf(type);
    }

    @Override
    public JavadocComment getJavaDoc() {
        if(getComment() instanceof JavadocComment){
            return (JavadocComment) getComment();
        }
        return null;
    }
}
