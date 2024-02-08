/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

import java.util.Optional;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.observer.ObservableProperty;

/**
 * The removal of an element from a list.
 */
public class ListRemovalChange implements Change {

    private final ObservableProperty observableProperty;

    private final int index;

    public ListRemovalChange(ObservableProperty observableProperty, int index) {
        this.observableProperty = observableProperty;
        this.index = index;
    }

    @Override
    public Object getValue(ObservableProperty property, Node node) {
        if (property == observableProperty) {
            Object currentRawValue = new NoChange().getValue(property, node);
            if (currentRawValue instanceof Optional) {
                Optional<?> optional = (Optional<?>) currentRawValue;
                currentRawValue = optional.orElse(null);
            }
            if (!(currentRawValue instanceof NodeList)) {
                throw new IllegalStateException("Expected NodeList, found " + currentRawValue.getClass().getCanonicalName());
            }
            NodeList<Node> currentNodeList = (NodeList<Node>) currentRawValue;
            // Note: When adding to a node list children get assigned the list's parent, thus we must set the list's parent before adding children (#2592).
            NodeList<Node> newNodeList = new NodeList<>();
            // fix #2187 set the parent node in the new list
            newNodeList.setParentNode(currentNodeList.getParentNodeForChildren());
			// Here we want to obtain a sub-list that does not contain an element.
			// It is important not to implement this by first adding all the elements in the
			// list and then deleting the element to be removed, as this involves event
			// propagation mechanisms, particularly for lexical preservation,
			// which deletes the relationship between a node and its parent node.
			// This relationship is necessary to reinforce indentation, for example when
			// deleting a node, as indentation can be carried by the parent node.
            currentNodeList.stream().filter(n -> !isSameNode(currentNodeList.get(index),n))
            	.forEach(selectedNode -> newNodeList.add(selectedNode));
            return newNodeList;
        }
        return new NoChange().getValue(property, node);
    }

    private boolean isSameNode(Node n1, Node n2) {
    	return n1.equals(n2) && isSameRange(n1, n2);
    }

    private boolean isSameRange(Node n1, Node n2) {
    	return (!n1.hasRange() && !n2.hasRange())
    			|| (n1.hasRange() && n2.hasRange() && isSameRange(n1.getRange().get(), n2.getRange().get()));
    }

	private boolean isSameRange(Range r1, Range r2) {
    	return r1.equals(r2);
    }

    @Override
	public ObservableProperty getProperty() {
		return observableProperty;
	}
}
