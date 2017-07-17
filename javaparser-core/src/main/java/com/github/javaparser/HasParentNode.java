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

package com.github.javaparser;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.Observable;

import java.util.Optional;

/**
 * An object that has a parent node.
 */
public interface HasParentNode<T> extends Observable {

    /**
     * Return the parent node or null, if no parent is set.
     */
    Optional<Node> getParentNode();

    /**
     * Set the parent node.
     *
     * @param parentNode the parent node or null, to set no parent
     * @return return <i>this</i>
     */
    T setParentNode(Node parentNode);

    /**
     * <i>this</i> for everything except NodeLists. NodeLists use their parent as their children parent.
     */
    Node getParentNodeForChildren();

    /**
     * Get the ancestor of the node having the given type, or null if no ancestor of the given type is found.
     */
    default <N> Optional<N> getAncestorOfType(Class<N> classType) {
        Node parent = getParentNode().orElse(null);
        while (parent != null) {
            if (classType.isAssignableFrom(parent.getClass())) {
                return Optional.of(classType.cast(parent));
            }
            parent = parent.getParentNode().orElse(null);
        }
        return Optional.empty();
    }
}
