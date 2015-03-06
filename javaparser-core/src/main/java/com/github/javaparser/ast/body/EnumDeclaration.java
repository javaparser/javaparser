/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.ast.body;

import com.github.javaparser.ast.DocumentableNode;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.lexical.Comment;
import com.github.javaparser.ast.lexical.CommentAttributes;
import com.github.javaparser.ast.lexical.Lexeme;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class EnumDeclaration extends TypeDeclaration implements DocumentableNode{

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

    public EnumDeclaration(Lexeme first, Lexeme last, int modifiers, List<AnnotationExpr> annotations, String name, List<ClassOrInterfaceType> implementsList, List<EnumConstantDeclaration> entries, List<BodyDeclaration> members) {
        super(first, last, annotations, modifiers, name, members);
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
        return entries;
    }

    public List<ClassOrInterfaceType> getImplements() {
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

    @Override
    public void setJavaDoc(Comment javadoc) {
        CommentAttributes comments = getCommentAttributes();
        if (comments == null) {
            comments = new CommentAttributes();
            setCommentAttributes(comments);
        }
        comments.setJavadocComment(javadoc);
    }

    @Override
    public Comment getJavaDoc() {
        return getCommentAttributes().getJavadocComment();
    }
}
