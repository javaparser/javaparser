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

import java.util.*;

/**
 * Iterate over all the nodes in (a part of) the AST.
 */
public abstract class TreeVisitor {

    public void visitLeavesFirst(Node node) {
        visitPostOrder(node);
    }

    /**
     * Performs a pre-order node traversal starting with a given node. When each node is visited, {@link #process(Node)}
     * is called for further processing.
     *
     * @param node The node at which the traversal begins.
     * @see <a href="https://en.wikipedia.org/wiki/Pre-order">Pre-order traversal</a>
     */
    public void visitPreOrder(Node node) {
        new PreOrderIterator(node).forEachRemaining(this::process);
    }

    public static class BreadthFirstIterator implements Iterator<Node> {
        private final Queue<Node> queue = new LinkedList<>();

        public BreadthFirstIterator(Node node) {
            queue.add(node);
        }

        @Override
        public boolean hasNext() {
            return !queue.isEmpty();
        }

        @Override
        public Node next() {
            Node next = queue.remove();
            queue.addAll(next.getChildNodes());
            return next;
        }
    }

    public static class PreOrderIterator implements Iterator<Node> {
        private final Stack<Node> stack = new Stack<>();

        public PreOrderIterator(Node node) {
            stack.add(node);
        }

        @Override
        public boolean hasNext() {
            return !stack.isEmpty();
        }

        @Override
        public Node next() {
            Node next = stack.pop();
            List<Node> children = next.getChildNodes();
            for (int i = children.size() - 1; i >= 0; i--) {
                stack.add(children.get(i));
            }
            return next;
        }
    }

    public static class PostOrderIterator implements Iterator<Node> {
        private final Stack<List<Node>> nodesStack = new Stack<>();
        private final Stack<Integer> cursorStack = new Stack<>();
        private final Node root;
        private boolean hasNext = true;

        public PostOrderIterator(Node root) {
            this.root = root;
            fillStackToLeaf(root);
        }

        private void fillStackToLeaf(Node node) {
            while (true) {
                List<Node> childNodes = new ArrayList<>(node.getChildNodes());
                if (childNodes.isEmpty()) {
                    break;
                }
                nodesStack.push(childNodes);
                cursorStack.push(0);
                node = childNodes.get(0);
            }
        }

        @Override
        public boolean hasNext() {
            return hasNext;
        }

        @Override
        public Node next() {
            final List<Node> nodes = nodesStack.peek();
            final int cursor = cursorStack.peek();
            final boolean levelHasNext = cursor < nodes.size();
            if (levelHasNext) {
                Node node = nodes.get(cursor);
                fillStackToLeaf(node);
                return nextFromLevel();
            } else {
                nodesStack.pop();
                cursorStack.pop();
                hasNext = !nodesStack.empty();
                if (hasNext) {
                    return nextFromLevel();
                }
                return root;
            }
        }

        private Node nextFromLevel() {
            final List<Node> nodes = nodesStack.peek();
            final int cursor = cursorStack.pop();
            cursorStack.push(cursor + 1);
            return nodes.get(cursor);
        }
    }

    /**
     * Performs a post-order node traversal starting with a given node. When each node is visited, {@link
     * #process(Node)} is called for further processing.
     *
     * @param node The node at which the traversal begins.
     * @see <a href="https://en.wikipedia.org/wiki/Post-order">Post-order traversal</a>
     */
    public void visitPostOrder(Node node) {
        new PostOrderIterator(node).forEachRemaining(this::process);
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
        new BreadthFirstIterator(node).forEachRemaining(this::process);
    }

    /**
     * Process the given node.
     *
     * @param node The current node to process.
     */
    public abstract void process(Node node);
}
