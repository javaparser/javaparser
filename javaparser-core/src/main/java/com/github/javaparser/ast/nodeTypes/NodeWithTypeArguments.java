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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.type.Type;

import java.util.*;

import static com.github.javaparser.utils.Utils.arrayToList;

/**
 * A node that can have type arguments.
 * <pre>
 *     new X();        --> typeArguments == null
 *     new X&lt;>();      --> typeArguments.types = [], typeArguments.diamondOperator=true 
 *     new X&lt;C,D>();   --> typeArguments.types = [C,D], typeArguments.diamondOperator=false 
 * </pre>
 */
public interface NodeWithTypeArguments<T> {
    /**
     * @return the types that can be found in the type arguments: &lt;String, Integer>.
     */
    List<Type<?>> getTypeArguments();

    /**
     * Allows you to set the generic arguments
     * @param typeArguments The list of types of the generics
     */
    T setTypeArguments(List<Type<?>> typeArguments);

    /**
     * @return whether the type arguments look like &lt;>.
     */
    default boolean isUsingDiamondOperator() {
        if(getTypeArguments()==null){
            return false;
        }
        return getTypeArguments().isEmpty();
    }

    /**
     * Sets the type arguments to &lt>.
     */
    default T setDiamondOperator() {
        final List<Type<?>> empty = new LinkedList<>();
        setTypeArguments(empty);
        return (T) this;
    }

    /**
     * Removes all type arguments, including the surrounding &lt;>.
     */
    default T removeTypeArguments() {
        setTypeArguments((List<Type<?>>) null);
        return (T) this;
    }

    default T setTypeArguments(Type<?>... typeArguments) {
        setTypeArguments(arrayToList(typeArguments));
        return (T) this;
    }
}
