/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class ClassOrInterfaceType extends Type {

    private ClassOrInterfaceType scope;

    private String name;

    private List<Type> typeArgs;

    public ClassOrInterfaceType() {
    }

    public ClassOrInterfaceType(final String name) {
        setName(name);
    }

    public ClassOrInterfaceType(final ClassOrInterfaceType scope, final String name) {
        setScope(scope);
        setName(name);
    }

    public ClassOrInterfaceType(final int beginLine, final int beginColumn, final int endLine, final int endColumn,
                                final ClassOrInterfaceType scope, final String name, final List<Type> typeArgs) {
        super(beginLine, beginColumn, endLine, endColumn);
        setScope(scope);
        setName(name);
        setTypeArgs(typeArgs);
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    public String getName() {
        return name;
    }

    public ClassOrInterfaceType getScope() {
        return scope;
    }

    public List<Type> getTypeArgs() {
        return typeArgs;
    }

    public boolean isBoxedType() {
        return PrimitiveType.unboxMap.containsKey(name);
    }

    public PrimitiveType toUnboxedType() throws UnsupportedOperationException {
        if (!isBoxedType()) throw new UnsupportedOperationException(name + " isn't a boxed type.");
        return new PrimitiveType(PrimitiveType.unboxMap.get(name));
    }

    public void setName(final String name) {
        this.name = name;
    }

    public void setScope(final ClassOrInterfaceType scope) {
        this.scope = scope;
        setAsParentNodeOf(this.scope);
    }

    public void setTypeArgs(final List<Type> typeArgs) {
        this.typeArgs = typeArgs;
        setAsParentNodeOf(this.typeArgs);
    }
}
