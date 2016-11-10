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
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A name that may consist of multiple identifiers.
 * In other words: it.may.contain.dots.
 * <p>
 * The rightmost identifier is "id",
 * The one to the left of it is "qualifier.id", etc.
 * <p>
 * You can construct one from a String with the name(...) method.
 *
 * @see SimpleName
 * @author Julio Vilmar Gesser
 */
public class Name extends Node {
    private String id;
    // TODO nullable
    private Name qualifier;

    public Name() {
        this(Range.UNKNOWN, null, "empty");
    }

    public Name(final String id) {
        this(Range.UNKNOWN, null, id);
    }

    public Name(Name qualifier, final String id) {
        this(Range.UNKNOWN, qualifier, id);
    }

    public Name(Range range, Name qualifier, final String id) {
        super(range);
        setId(id);
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

    public final String getId() {
        return id;
    }

    public Name setId(final String id) {
        this.id = assertNotNull(id);
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
        String[] split = qualifiedName.split("\\.");
        Name ret = new Name(split[0]);
        for (int i = 1; i < split.length; i++) {
            ret = new Name(ret, split[i]);
        }
        return ret;
    }

    public Name getQualifier() {
        return qualifier;
    }

    public Name setQualifier(final Name qualifier) {
        this.qualifier = qualifier;
        setAsParentNodeOf(qualifier);
        return this;
    }
}
