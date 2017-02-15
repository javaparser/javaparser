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
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.metamodel.DerivedProperty;

import java.util.Optional;

import static com.github.javaparser.ast.NodeList.nodeList;

/**
 * A node that can have type arguments.
 * <p>
 * <pre>
 *     new X();        --> typeArguments == Optional is empty
 *     new X&lt;>();      --> typeArguments = [], diamondOperator = true
 *     new X&lt;C,D>();   --> typeArguments = [C,D], diamondOperator = false
 * </pre>
 */
public interface NodeWithTypeArguments<N extends Node> {
    /**
     * @return the types that can be found in the type arguments: &lt;String, Integer&gt;.
     */
    Optional<NodeList<Type>> getTypeArguments();

    /**
     * Allows you to set the generic arguments
     *
     * @param typeArguments The list of types of the generics, can be null
     */
    N setTypeArguments(NodeList<Type> typeArguments);

    /**
     * @return whether the type arguments look like &lt;>.
     */
    @DerivedProperty
    default boolean isUsingDiamondOperator() {
        return getTypeArguments().isPresent() && getTypeArguments().get().isEmpty();
    }

    /**
     * Sets the type arguments to &lt>.
     */
    @SuppressWarnings("unchecked")
    default N setDiamondOperator() {
        return setTypeArguments(new NodeList<>());
    }

    /**
     * Removes all type arguments, including the surrounding &lt;>.
     */
    @SuppressWarnings("unchecked")
    default N removeTypeArguments() {
        return setTypeArguments((NodeList<Type>) null);
    }

    @SuppressWarnings("unchecked")
    default N setTypeArguments(Type... typeArguments) {
        return setTypeArguments(nodeList(typeArguments));
    }
}
