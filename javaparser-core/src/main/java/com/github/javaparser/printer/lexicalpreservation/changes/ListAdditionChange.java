/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

/**
 * The Addition of an element to a list.
 */
public class ListAdditionChange implements Change {
    private final ObservableProperty observableProperty;
    private final int index;
    private final Node nodeAdded;

    public ListAdditionChange(ObservableProperty observableProperty, int index, Node nodeAdded) {
        this.observableProperty = observableProperty;
        this.index = index;
        this.nodeAdded = nodeAdded;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            NodeList<Node> nodeList = new NodeList<>();
	    nodeList.setParentNode(node);
            Object currentRawValue = new NoChange().getValue(property, node);
            if (!(currentRawValue instanceof NodeList)){
                throw new IllegalStateException("Expected NodeList, found " + currentRawValue.getClass().getCanonicalName());
            }
            NodeList<?> currentNodeList = (NodeList<?>)(currentRawValue);
            nodeList.addAll(currentNodeList);
            nodeList.add(index, nodeAdded);
            return nodeList;
        } else {
            return new NoChange().getValue(property, node);
        }
    }
}
