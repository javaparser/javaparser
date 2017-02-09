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
import com.github.javaparser.ast.nodeTypes.NodeWithBlockStmt;
import com.github.javaparser.ast.nodeTypes.NodeWithJavadoc;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;

/**
 * A (possibly static) initializer body. "static { a=3; }" in this example: <code>class X { static { a=3; }  } </code>
 *
 * @author Julio Vilmar Gesser
 */
public final class InitializerDeclaration extends BodyDeclaration<InitializerDeclaration> implements NodeWithJavadoc<InitializerDeclaration>, NodeWithBlockStmt<InitializerDeclaration> {

    private boolean isStatic;

    private BlockStmt body;

    public InitializerDeclaration() {
        this(null, false, new BlockStmt());
    }

    @AllFieldsConstructor
    public InitializerDeclaration(boolean isStatic, BlockStmt body) {
        this(null, isStatic, body);
    }

    public InitializerDeclaration(Range range, boolean isStatic, BlockStmt body) {
        super(range, new NodeList<>());
        setStatic(isStatic);
        setBody(body);
    }

    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        v.visit(this, arg);
    }

    public BlockStmt getBody() {
        return body;
    }

    public boolean isStatic() {
        return isStatic;
    }

    public InitializerDeclaration setBody(final BlockStmt body) {
        assertNotNull(body);
        notifyPropertyChange(ObservableProperty.BODY, this.body, body);
        if (this.body != null)
            this.body.setParentNode(null);
        this.body = body;
        setAsParentNodeOf(body);
        return this;
    }

    public InitializerDeclaration setStatic(final boolean isStatic) {
        notifyPropertyChange(ObservableProperty.STATIC, this.isStatic, isStatic);
        this.isStatic = isStatic;
        return this;
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
    public InitializerDeclaration clone() {
        return (InitializerDeclaration) accept(new CloneVisitor(), null);
    }
}

