/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation.changes;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;

import java.util.Optional;

/**
 * The replacement of an element in a list.
 */
public class ListReplacementChange implements Change {

    private final ObservableProperty observableProperty;
    private final int index;
    private final Node newValue;

    public ListReplacementChange(ObservableProperty observableProperty, int index, Node newValue) {
        this.observableProperty = observableProperty;
        this.index = index;
        this.newValue = newValue;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            Object currentRawValue = new NoChange().getValue(property, node);
            if (currentRawValue instanceof Optional) {
                Optional<?> optional = (Optional<?>) currentRawValue;
                currentRawValue = optional.orElseGet(null);
            }
            if (!(currentRawValue instanceof NodeList)) {
                throw new IllegalStateException("Expected NodeList, found " + currentRawValue.getClass().getCanonicalName());
            }
            NodeList<Node> currentNodeList = (NodeList<Node>) currentRawValue;

            // Note: When adding to a node list children get assigned the list's parent, thus we must set the list's parent before adding children (#2592).
            NodeList<Node> newNodeList = new NodeList<>();
            newNodeList.setParentNode(currentNodeList.getParentNodeForChildren());
            newNodeList.addAll(currentNodeList);

            // Perform modification -- replace an item in the list
            newNodeList.set(index, newValue);

            return newNodeList;
        } else {
            return new NoChange().getValue(property, node);
        }
    }
}
