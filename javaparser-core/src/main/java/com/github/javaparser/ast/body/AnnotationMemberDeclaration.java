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

import com.github.javaparser.Range;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.nodeTypes.NodeWithType;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.EnumSet;

import static com.github.javaparser.ast.NodeList.*;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class AnnotationMemberDeclaration extends BodyDeclaration<AnnotationMemberDeclaration> implements NodeWithJavaDoc<AnnotationMemberDeclaration>, NodeWithName<AnnotationMemberDeclaration>,
        NodeWithType<AnnotationMemberDeclaration>, NodeWithModifiers<AnnotationMemberDeclaration> {

    private EnumSet<Modifier> modifiers = EnumSet.noneOf(Modifier.class);

    private Type<?> type;

    private String name;

    // TODO nullable
    private Expression defaultValue;

    public AnnotationMemberDeclaration() {
        this(Range.UNKNOWN,
                EnumSet.noneOf(Modifier.class),
                new NodeList<>(),
                new ClassOrInterfaceType(),
                "",
                null);
    }

    public AnnotationMemberDeclaration(EnumSet<Modifier> modifiers, Type<?> type, String name, Expression defaultValue) {
        this(Range.UNKNOWN,
                modifiers,
                new NodeList<>(),
                type,
                name,
                defaultValue);
    }

    public AnnotationMemberDeclaration(EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, Type<?> type, String name,
                                       Expression defaultValue) {
        this(Range.UNKNOWN,
                modifiers,
                annotations,
                type,
                name,
                defaultValue);
    }

    public AnnotationMemberDeclaration(Range range, EnumSet<Modifier> modifiers, NodeList<AnnotationExpr> annotations, Type type,
                                       String name, Expression defaultValue) {
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
     * @see Modifier
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
    public Type<?> getType() {
        return type;
    }

    public AnnotationMemberDeclaration setDefaultValue(Expression defaultValue) {
        this.defaultValue = defaultValue;
        setAsParentNodeOf(defaultValue);
        return this;
    }

    @Override
    public AnnotationMemberDeclaration setModifiers(EnumSet<Modifier> modifiers) {
        this.modifiers = assertNotNull(modifiers);
        return this;
    }

    @Override
    public AnnotationMemberDeclaration setName(String name) {
        this.name = assertNotNull(name);
        return this;
    }

    @Override
    public AnnotationMemberDeclaration setType(Type<?> type) {
        this.type = assertNotNull(type);
        setAsParentNodeOf(type);
        return this;
    }

    @Override
    public JavadocComment getJavaDoc() {
        if (getComment() instanceof JavadocComment) {
            return (JavadocComment) getComment();
        }
        return null;
    }
}
