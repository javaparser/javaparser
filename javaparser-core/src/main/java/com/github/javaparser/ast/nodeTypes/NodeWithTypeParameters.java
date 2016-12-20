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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.type.TypeParameter;

/**
 * A node that can have type parameters.
 * <pre>
 *     class X {}        --> typeParameters == []
 *     class X&lt;> {}      --> does not occur.
 *     class X&lt;C,D> {}   --> typeParameters = [C,D]
 * </pre>
 */
public interface NodeWithTypeParameters<N extends Node> {
    NodeList<TypeParameter> getTypeParameters();

    default TypeParameter getTypeParameter(int i) {
        return getTypeParameters().get(i);
    }

    @SuppressWarnings("unchecked")
    default N setTypeParameter(int i, TypeParameter typeParameter) {
        getTypeParameters().set(i, typeParameter);
        return (N) this;
    }

    @SuppressWarnings("unchecked")
    default N addTypeParameter(TypeParameter typeParameter) {
        getTypeParameters().add(typeParameter);
        return (N) this;
    }

    N setTypeParameters(NodeList<TypeParameter> typeParameters);

    default boolean isGeneric() {
        return getTypeParameters().size() > 0;
    }
}
