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
import java.util.function.Predicate;

/**
 * An object that can have a parent node.
 */
public interface HasParentNode<T> extends Observable {

    /**
     * Returns the parent node, or {@code Optional.empty} if no parent is set.
     */
    Optional<Node> getParentNode();

    /**
     * Sets the parent node.
     *
     * @param parentNode the parent node, or {@code null} to set no parent.
     * @return return {@code this}
     */
    T setParentNode(Node parentNode);

    /**
     * Returns the parent node from the perspective of the children of this node.
     * <p>
     * That is, this method returns {@code this} for everything except {@code NodeList}. A {@code NodeList} returns its
     * parent node instead. This is because a {@code NodeList} sets the parent of all its children to its own parent
     * node (see {@link com.github.javaparser.ast.NodeList} for details).
     */
    Node getParentNodeForChildren();

    /**
     * Walks the parents of this node and returns the first node of type {@code type}, or {@code empty()} if none is
     * found. The given type may also be an interface type, such as one of the {@code NodeWith...} interface types.
     */
    default <N> Optional<N> findAncestor(Class<N> type) {
        return findAncestor(type, x -> true);
    }

    /**
     * Walks the parents of this node and returns the first node of type {@code type} that matches {@code predicate}, or
     * {@code empty()} if none is found. The given type may also be an interface type, such as one of the
     * {@code NodeWith...} interface types.
     */
    default <N> Optional<N> findAncestor(Class<N> type, Predicate<N> predicate) {
        Optional<Node> possibleParent = getParentNode();
        while (possibleParent.isPresent()) {
            Node parent = possibleParent.get();
            if (type.isAssignableFrom(parent.getClass()) && predicate.test(type.cast(parent))) {
                return Optional.of(type.cast(parent));
            }
            possibleParent = parent.getParentNode();
        }
        return Optional.empty();
    }

}
