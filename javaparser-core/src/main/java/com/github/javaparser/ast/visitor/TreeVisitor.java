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

package com.github.javaparser.ast.visitor;

import com.github.javaparser.ast.Node;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;

/**
 * Iterate over all the nodes in (a part of) the AST. In contrast to the visit methods in Node, these methods are
 * implemented in a simple recursive way which should be more efficient. A disadvantage is that they cannot be quit in
 * the middle of their traversal.
 */
public abstract class TreeVisitor {

    public void visitLeavesFirst(Node node) {
        for (Node child : node.getChildNodes()) {
            visitLeavesFirst(child);
        }
        process(node);
    }

    /**
     * Performs a pre-order node traversal starting with a given node. When each node is visited, {@link #process(Node)}
     * is called for further processing.
     *
     * @param node The node at which the traversal begins.
     * @see <a href="https://en.wikipedia.org/wiki/Pre-order">Pre-order traversal</a>
     */
    public void visitPreOrder(Node node) {
        process(node);
        new ArrayList<>(node.getChildNodes()).forEach(this::visitPreOrder);
    }

    /**
     * Performs a post-order node traversal starting with a given node. When each node is visited, {@link
     * #process(Node)} is called for further processing.
     *
     * @param node The node at which the traversal begins.
     * @see <a href="https://en.wikipedia.org/wiki/Post-order">Post-order traversal</a>
     */
    public void visitPostOrder(Node node) {
        new ArrayList<>(node.getChildNodes()).forEach(this::visitPostOrder);
        process(node);
    }

    /**
     * Performs a pre-order node traversal starting with a given node. When each node is visited, {@link #process(Node)}
     * is called for further processing.
     *
     * @param node The node at which the traversal begins.
     * @see <a href="https://en.wikipedia.org/wiki/Pre-order">Pre-order traversal</a>
     * @deprecated As of release 3.1.0, replaced by {@link #visitPreOrder(Node)}
     */
    @Deprecated
    public void visitDepthFirst(Node node) {
        visitPreOrder(node);
    }

    /**
     * https://en.wikipedia.org/wiki/Breadth-first_search
     *
     * @param node the start node, and the first one that is passed to process(node).
     */
    public void visitBreadthFirst(Node node) {
        final Queue<Node> queue = new LinkedList<>();
        queue.offer(node);
        while (queue.size() > 0) {
            final Node head = queue.peek();
            for (Node child : head.getChildNodes()) {
                queue.offer(child);
            }
            process(queue.poll());
        }
    }

    /**
     * Process the given node.
     *
     * @param node The current node to process.
     */
    public abstract void process(Node node);

    /**
     * Performs a simple traversal over all nodes that have the passed node as their parent.
     */
    public void visitDirectChildren(Node node) {
        new ArrayList<>(node.getChildNodes()).forEach(this::process);
    }
}
