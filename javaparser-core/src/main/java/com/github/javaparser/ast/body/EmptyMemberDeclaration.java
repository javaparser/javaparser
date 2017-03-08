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
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.EmptyMemberDeclarationMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A loose ";" inside a body.<br/><code>class X { ; }</code>
 *
 * @author Julio Vilmar Gesser
 * @deprecated these ;'s should be ignored
 */
@Deprecated
public final class EmptyMemberDeclaration extends BodyDeclaration<EmptyMemberDeclaration> implements NodeWithJavadoc<EmptyMemberDeclaration> {

    @AllFieldsConstructor
    public EmptyMemberDeclaration() {
        this(null);
    }

    public EmptyMemberDeclaration(Range range) {
        super(range, new NodeList<>());
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    @Override
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getAnnotations());
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public EmptyMemberDeclaration clone() {
        return (EmptyMemberDeclaration) accept(new CloneVisitor(), null);
    }

    @Override
    public EmptyMemberDeclarationMetaModel getMetaModel() {
        return JavaParserMetaModel.emptyMemberDeclarationMetaModel;
    }
}
