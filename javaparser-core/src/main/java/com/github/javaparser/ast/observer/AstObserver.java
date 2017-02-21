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

package com.github.javaparser.ast.observer;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;

/**
 * An Observer for an AST element (either a Node or a NodeList).
 */
public interface AstObserver {

    /**
     * Type of change occurring on a List
     */
    enum ListChangeType {
        ADDITION,
        REMOVAL
    }

    /**
     * The value of a property is changed
     *
     * @param observedNode owner of the property
     * @param property property changed
     * @param oldValue value of the property before the change
     * @param newValue value of the property after the change
     */
    void propertyChange(Node observedNode, ObservableProperty property, Object oldValue, Object newValue);

    /**
     * The parent of a node is changed
     *
     * @param observedNode node of which the parent is changed
     * @param previousParent previous parent
     * @param newParent new parent
     */
    void parentChange(Node observedNode, Node previousParent, Node newParent);

    /**
     * A list is changed
     *
     * @param observedNode list changed
     * @param type type of change
     * @param index position at which the changed occurred
     * @param nodeAddedOrRemoved element added or removed
     */
    void listChange(NodeList observedNode, ListChangeType type, int index, Node nodeAddedOrRemoved);

    void listReplacement(NodeList observedNode, int index, Node oldNode, Node newNode);
}
