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
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

import static com.github.javaparser.utils.Utils.ensureNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class EnumConstantDeclaration extends BodyDeclaration<EnumConstantDeclaration>
        implements NodeWithJavaDoc<EnumConstantDeclaration>, NodeWithName<EnumConstantDeclaration> {

    private String name;

    private List<Expression> argsList;

    private List<BodyDeclaration<?>> classBodyList;

    public EnumConstantDeclaration() {
    }

    public EnumConstantDeclaration(String name) {
        setName(name);
    }

    public EnumConstantDeclaration(List<AnnotationExpr> annotations, String name, List<Expression> argsList,
                                   List<BodyDeclaration<?>> classBodyList) {
        super(annotations);
        setName(name);
        setArgsList(argsList);
        setClassBodyList(classBodyList);
    }

    public EnumConstantDeclaration(Range range, List<AnnotationExpr> annotations, String name, List<Expression> argsList,
                                   List<BodyDeclaration<?>> classBodyList) {
        super(range, annotations);
        setName(name);
        setArgsList(argsList);
        setClassBodyList(classBodyList);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public List<Expression> getArgsList() {
        argsList = ensureNotNull(argsList);
        return argsList;
    }

    public List<BodyDeclaration<?>> getClassBodyList() {
        classBodyList = ensureNotNull(classBodyList);
        return classBodyList;
    }

    @Override
    public String getName() {
        return name;
    }

    public void setArgsList(List<Expression> argsList) {
        this.argsList = argsList;
		setAsParentNodeOf(this.argsList);
    }

    public void setClassBodyList(List<BodyDeclaration<?>> classBodyList) {
        this.classBodyList = classBodyList;
		setAsParentNodeOf(this.classBodyList);
    }

    @Override
    public EnumConstantDeclaration setName(String name) {
        this.name = name;
        return this;
    }

    @Override
    public JavadocComment getJavaDoc() {
        if(getComment() instanceof JavadocComment){
            return (JavadocComment) getComment();
        }
        return null;
    }

    public EnumConstantDeclaration addArgument(String valueExpr) {
        getArgsList().add(NameExpr.create(valueExpr));
        return this;
    }
}
