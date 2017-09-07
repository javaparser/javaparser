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
package com.github.javaparser.ast.expr;

import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.NameExprMetaModel;
import javax.annotation.Generated;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.metamodel.QualifiedNameExprMetaModel;

/**
 * Whenever a Name is used in an expression, it is wrapped in QualifiedNameExpr.
 * <br/>In <code>try(a.b.c){}</code> a.b.c is a Name inside a QualifiedNameExpr.
 */
public final class QualifiedNameExpr extends Expression implements NodeWithName<QualifiedNameExpr> {

    private Name name;

    public QualifiedNameExpr() {
        this(null, new Name());
    }

    public QualifiedNameExpr(final String name) {
        this(null, new Name(name));
    }

    @AllFieldsConstructor
    public QualifiedNameExpr(final Name name) {
        this(name.getTokenRange().orElse(null), name);
        setRange(name.getRange().orElse(null));
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public QualifiedNameExpr(TokenRange tokenRange, Name name) {
        super(tokenRange);
        setName(name);
        customInitialization();
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return null;
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Name getName() {
        return name;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public QualifiedNameExpr setName(final Name name) {
        assertNotNull(name);
        if (name == this.name) {
            return (QualifiedNameExpr) this;
        }
        notifyPropertyChange(ObservableProperty.NAME, this.name, name);
        if (this.name != null)
            this.name.setParentNode(null);
        this.name = name;
        setAsParentNodeOf(name);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public QualifiedNameExpr clone() {
        return (QualifiedNameExpr) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public QualifiedNameExprMetaModel getMetaModel() {
        return JavaParserMetaModel.qualifiedNameExprMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        if (node == name) {
            setName((Name) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }
}
