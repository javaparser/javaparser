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
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.LinkedList;
import java.util.List;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * One of the values an enum can take. A(1) and B(2) in this example: <code>enum X { A(1), B(2) }</code>
 *
 * @author Julio Vilmar Gesser
 */
public final class EnumConstantDeclaration extends BodyDeclaration<EnumConstantDeclaration> implements
        NodeWithJavadoc<EnumConstantDeclaration>,
        NodeWithSimpleName<EnumConstantDeclaration>,
        NodeWithArguments<EnumConstantDeclaration> {

    private SimpleName name;

    private NodeList<Expression> arguments;

    private NodeList<BodyDeclaration<?>> classBody;

    public EnumConstantDeclaration() {
        this(null,
                new NodeList<>(),
                new SimpleName(),
                new NodeList<>(),
                new NodeList<>());
    }

    public EnumConstantDeclaration(String name) {
        this(null,
                new NodeList<>(),
                new SimpleName(name),
                new NodeList<>(),
                new NodeList<>());
    }

    public EnumConstantDeclaration(NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<Expression> arguments,
                                   NodeList<BodyDeclaration<?>> classBody) {
        this(null, annotations, name, arguments, classBody);
    }

    public EnumConstantDeclaration(Range range, NodeList<AnnotationExpr> annotations, SimpleName name, NodeList<Expression> arguments,
                                   NodeList<BodyDeclaration<?>> classBody) {
        super(range, annotations);
        setName(name);
        setArguments(arguments);
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

    public NodeList<Expression> getArguments() {
        return arguments;
    }

    public NodeList<BodyDeclaration<?>> getClassBody() {
        return classBody;
    }

    @Override
    public SimpleName getName() {
        return name;
    }

    public EnumConstantDeclaration setArguments(NodeList<Expression> arguments) {
        notifyPropertyChange(ObservableProperty.ARGUMENTS, this.arguments, arguments);
        this.arguments = assertNotNull(arguments);
        setAsParentNodeOf(this.arguments);
        return this;
    }

    public EnumConstantDeclaration setClassBody(NodeList<BodyDeclaration<?>> classBody) {
        notifyPropertyChange(ObservableProperty.CLASS_BODY, this.classBody, classBody);
        this.classBody = assertNotNull(classBody);
        setAsParentNodeOf(this.classBody);
        return this;
    }

    @Override
    public EnumConstantDeclaration setName(SimpleName name) {
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        this.name = assertNotNull(name);
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    public JavadocComment getJavadocComment() {
        if (getComment().isPresent() && getComment().get() instanceof JavadocComment) {
            return (JavadocComment) getComment().get();
        }
        return null;
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        List<NodeList<?>> res = new LinkedList<>(super.getNodeLists());
        res.add(arguments);
        res.add(classBody);
        return res;
    }
}
