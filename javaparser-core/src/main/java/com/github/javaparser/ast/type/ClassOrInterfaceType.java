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

package com.github.javaparser.ast.type;

import java.util.Optional;

import com.github.javaparser.Range;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.nodeTypes.NodeWithAnnotations;
import com.github.javaparser.ast.nodeTypes.NodeWithName;
import com.github.javaparser.ast.nodeTypes.NodeWithTypeArguments;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceType extends ReferenceType<ClassOrInterfaceType> implements
        NodeWithName<ClassOrInterfaceType>,
        NodeWithAnnotations<ClassOrInterfaceType>,
        NodeWithTypeArguments<ClassOrInterfaceType> {

    private ClassOrInterfaceType scope;

    private String name;

    private NodeList<Type<?>> typeArguments;

    public ClassOrInterfaceType() {
        this(Range.UNKNOWN,
                null,
                "empty",
                null);
    }

    public ClassOrInterfaceType(final String name) {
        this(Range.UNKNOWN,
                null,
                name,
                null);
    }

    public ClassOrInterfaceType(final ClassOrInterfaceType scope, final String name) {
        this(Range.UNKNOWN,
                scope,
                name,
                null);
    }

    public ClassOrInterfaceType(final Range range, final ClassOrInterfaceType scope, final String name,
                                final NodeList<Type<?>> typeArguments) {
        super(range);
        setScope(scope);
        setName(name);
        setTypeArguments(typeArguments);
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
    public String getName() {
        return name;
    }

    public Optional<ClassOrInterfaceType> getScope() {
        return Optional.ofNullable(scope);
    }

    public boolean isBoxedType() {
        return PrimitiveType.unboxMap.containsKey(name);
    }

    public PrimitiveType toUnboxedType() throws UnsupportedOperationException {
        if (!isBoxedType()) {
            throw new UnsupportedOperationException(name + " isn't a boxed type.");
        }
        return new PrimitiveType(PrimitiveType.unboxMap.get(name));
    }

    @Override
    public ClassOrInterfaceType setName(final String name) {
        this.name = name;
        return this;
    }

    /**
     * Sets the scope
     * 
     * @param scope the scope, can be null
     * @return this, the ClassOrInterfaceType
     */
    public ClassOrInterfaceType setScope(final ClassOrInterfaceType scope) {
        this.scope = scope;
        setAsParentNodeOf(this.scope);
        return this;
    }

    @Override
    public Optional<NodeList<Type<?>>> getTypeArguments() {
        return Optional.ofNullable(typeArguments);
    }

    /**
     * Sets the typeArguments
     * 
     * @param typeArguments the typeArguments, can be null
     * @return this, the ClassOrInterfaceType
     */
    @Override
    public ClassOrInterfaceType setTypeArguments(final NodeList<Type<?>> types) {
        this.typeArguments = types;
        setAsParentNodeOf(this.typeArguments);
        return this;
    }
}
