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

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNonEmpty;

/**
 * A name that may consist of multiple identifiers.
 * In other words: it.may.contain.dots.
 * <p>
 * The rightmost identifier is "identifier",
 * The one to the left of it is "qualifier.identifier", etc.
 * <p>
 * You can construct one from a String with the name(...) method.
 *
 * @author Julio Vilmar Gesser
 * @see SimpleName
 */
public class Name extends Node implements NodeWithIdentifier<Name> {
    private String identifier;
    private Name qualifier;

    public Name() {
        this(null, null, "empty");
    }

    public Name(final String identifier) {
        this(null, null, identifier);
    }

    @AllFieldsConstructor
    public Name(Name qualifier, final String identifier) {
        this(null, qualifier, identifier);
    }

    public Name(Range range, Name qualifier, final String identifier) {
        super(range);
        setIdentifier(identifier);
        setQualifier(qualifier);
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
    public Name setIdentifier(final String identifier) {
        assertNonEmpty(identifier);
        notifyPropertyChange(ObservableProperty.IDENTIFIER, this.identifier, identifier);
        this.identifier = identifier;
        return this;
    }

    /**
     * Creates a new {@link Name} from a qualified name.<br>
     * The qualified name can contains "." (dot) characters.
     *
     * @param qualifiedName qualified name
     * @return instanceof {@link Name}
     */
    public static Name parse(String qualifiedName) {
        assertNonEmpty(qualifiedName);
        String[] split = qualifiedName.split("\\.");
        Name ret = new Name(split[0]);
        for (int i = 1; i < split.length; i++) {
            ret = new Name(ret, split[i]);
        }
        return ret;
    }

    /**
     * @return the complete qualified name. Only the identifiers and the dots, so no comments or whitespace.
     */
    public String asString() {
        if (qualifier != null) {
            return qualifier.asString() + "." + identifier;
        }
        return identifier;
    }

    public Optional<Name> getQualifier() {
        return Optional.ofNullable(qualifier);
    }

    public Name setQualifier(final Name qualifier) {
        notifyPropertyChange(ObservableProperty.QUALIFIER, this.qualifier, qualifier);
        this.qualifier = qualifier;
        setAsParentNodeOf(qualifier);
        return this;
    }
}
