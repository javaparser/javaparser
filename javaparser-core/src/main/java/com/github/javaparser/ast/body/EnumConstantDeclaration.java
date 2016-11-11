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
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.ast.nodeTypes.NodeWithArguments;
import com.github.javaparser.ast.nodeTypes.NodeWithJavaDoc;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * @author Julio Vilmar Gesser
 */
public final class EnumConstantDeclaration extends BodyDeclaration<EnumConstantDeclaration> implements 
        NodeWithJavaDoc<EnumConstantDeclaration>,
        NodeWithSimpleName<EnumConstantDeclaration>,
        NodeWithArguments<EnumConstantDeclaration> {

    private SimpleName name;

    private NodeList<Expression> args;

    private NodeList<BodyDeclaration<?>> classBody;

    public EnumConstantDeclaration() {
        this(Range.UNKNOWN, 
                new NodeList<>(), 
                new SimpleName(),
                new NodeList<>(),
                new NodeList<>());
    }

    public EnumConstantDeclaration(String name) {
        this(Range.UNKNOWN, 
                new NodeList<>(),
                new SimpleName(name),
                new NodeList<>(),
                new NodeList<>());
    }

    public EnumConstantDeclaration(NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<Expression> args,
                                   NodeList<BodyDeclaration<?>> classBody) {
        this(Range.UNKNOWN, annotations, name, args, classBody);
    }

    public EnumConstantDeclaration(Range range, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<Expression> args,
                                   NodeList<BodyDeclaration<?>> classBody) {
        super(range, annotations);
        setName(name);
        setArgs(args);
        setClassBody(classBody);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public NodeList<Expression> getArgs() {
        return args;
    }

    public NodeList<BodyDeclaration<?>> getClassBody() {
        return classBody;
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    public EnumConstantDeclaration setArgs(NodeList<Expression> args) {
        notifyPropertyChange("args", this.args, args);
        this.args = assertNotNull(args);
		setAsParentNodeOf(this.args);
        return this;
    }

    public EnumConstantDeclaration setClassBody(NodeList<BodyDeclaration<?>> classBody) {
        notifyPropertyChange("classBody", this.classBody, classBody);
        this.classBody = assertNotNull(classBody);
		setAsParentNodeOf(this.classBody);
        return this;
    }

    @Override
    public EnumConstantDeclaration setName(SimpleName name) {
        notifyPropertyChange("name", this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    public JavadocComment getJavaDoc() {
        if(getComment() instanceof JavadocComment){
            return (JavadocComment) getComment();
        }
        return null;
    }
}
