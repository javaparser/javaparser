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

import com.github.javaparser.Range;
import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.nodeTypes.NodeWithIdentifier;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import static com.github.javaparser.utils.Utils.assertNonEmpty;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.SimpleNameMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * A name that consists of a single identifier.
 * In other words: it.does.NOT.contain.dots.
 *
 * @see Name
 */
public class SimpleName extends Node implements NodeWithIdentifier<SimpleName> {

    private String identifier;

    public SimpleName() {
        this(null, "empty");
    }

    @AllFieldsConstructor
    public SimpleName(final String identifier) {
        this(null, identifier);
    }

    public SimpleName(Range range, final String identifier) {
        super(range);
        setIdentifier(identifier);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Override
    public final String getIdentifier() {
        return identifier;
    }

    @Override
    public SimpleName setIdentifier(final String identifier) {
        assertNonEmpty(identifier);
        notifyPropertyChange(ObservableProperty.IDENTIFIER, this.identifier, identifier);
        this.identifier = identifier;
        return this;
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public SimpleName clone() {
        return (SimpleName) accept(new CloneVisitor(), null);
    }

    @Override
    public SimpleNameMetaModel getMetaModel() {
        return JavaParserMetaModel.simpleNameMetaModel;
    }
}
