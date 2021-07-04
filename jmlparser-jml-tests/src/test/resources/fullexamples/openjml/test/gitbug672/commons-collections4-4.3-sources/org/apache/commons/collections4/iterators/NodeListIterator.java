/*
 * Copyright 2013 The Apache Software Foundation.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.commons.collections4.iterators;

import java.util.Iterator;
import java.util.NoSuchElementException;

import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

/**
 * An {@link Iterator} over a {@link NodeList}.
 * <p>
 * This iterator does not support {@link #remove()} as a {@link NodeList} does not support
 * removal of items.
 *
 * @since 4.0
 * @see NodeList
 */
public class NodeListIterator implements Iterator<Node> {

    /** the original NodeList instance */
    private final NodeList nodeList;
    /** The current iterator index */
    private int index = 0;

    /**
     * Convenience constructor, which creates a new NodeListIterator from
     * the specified node's childNodes.
     *
     * @param node Node, who's child nodes are wrapped by this class. Must not be null
     * @throws NullPointerException if node is null
     */
    public NodeListIterator(final Node node) {
        if (node == null) {
            throw new NullPointerException("Node must not be null.");
        }
        this.nodeList = node.getChildNodes();
    }

    /**
     * Constructor, that creates a new NodeListIterator from the specified
     * <code>org.w3c.NodeList</code>
     *
     * @param nodeList node list, which is wrapped by this class. Must not be null
     * @throws NullPointerException if nodeList is null
     */
    public NodeListIterator(final NodeList nodeList) {
        if (nodeList == null) {
            throw new NullPointerException("NodeList must not be null.");
        }
        this.nodeList = nodeList;
    }

    @Override
    public boolean hasNext() {
        return nodeList == null ? false : index < nodeList.getLength();
    }

    @Override
    public Node next() {
        if (nodeList != null && index < nodeList.getLength()) {
            return nodeList.item(index++);
        }
        throw new NoSuchElementException("underlying nodeList has no more elements");
    }

    /**
     * Throws {@link UnsupportedOperationException}.
     *
     * @throws UnsupportedOperationException always
     */
    @Override
    public void remove() {
        throw new UnsupportedOperationException("remove() method not supported for a NodeListIterator.");
    }
}
