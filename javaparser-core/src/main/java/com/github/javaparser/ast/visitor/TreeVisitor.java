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
import java.util.List;
import java.util.Queue;

/**
 * Iterate over all the nodes in (a part of) the AST.
 */
public abstract class TreeVisitor {

    /**
     * https://en.wikipedia.org/wiki/Depth-first_search
     *
     * @param node the start node, and the first one that is passed to process(node).
     */
    public void visitDepthFirst(Node node) {
        process(node);
        final List<Node> copy = new ArrayList<>(node.getChildNodes());
        for (Node child : copy) {
            visitDepthFirst(child);
        }
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

    public abstract void process(Node node);
}
