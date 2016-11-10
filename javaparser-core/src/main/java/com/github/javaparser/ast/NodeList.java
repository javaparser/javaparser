package com.github.javaparser.ast;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import com.github.javaparser.HasParentNode;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * A list of nodes.
 *
 * @param <N> the type of nodes contained.
 */
public class NodeList<N extends Node> implements Iterable<N>, HasParentNode<NodeList<N>>, Visitable {
    private List<N> innerList = new ArrayList<>(0);

    private Node parentNode;

    public NodeList() {
        this(null);
    }

    public NodeList(Node parent) {
        setParentNode(parent);
    }

    public NodeList<N> add(N node) {
        own(node);
        innerList.add(node);
        return this;
    }

    private void own(N node) {
        if (node == null) {
            return;
        }
        setAsParentNodeOf(node);
    }

    public boolean remove(Node node) {
        boolean remove = innerList.remove(node);
        node.setParentNode(null);
        return remove;
    }

    public static <X extends Node> NodeList<X> nodeList(X... nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        for (X node : nodes) {
            nodeList.add(node);
        }
        return nodeList;
    }

    public static <X extends Node> NodeList<X> nodeList(Collection<X> nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        for (X node : nodes) {
            nodeList.add(node);
        }
        return nodeList;
    }

    public static <X extends Node> NodeList<X> nodeList(NodeList<X> nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        for (X node : nodes) {
            nodeList.add(node);
        }
        return nodeList;
    }

    public boolean contains(N node) {
        return innerList.contains(node);
    }

    public Stream<N> stream() {
        return innerList.stream();
    }

    public int size() {
        return innerList.size();
    }

    public N get(int i) {
        return innerList.get(i);
    }

    @Override
    public Iterator<N> iterator() {
        // TODO take care of "Iterator.remove"
        return innerList.iterator();
    }

    public NodeList<N> set(int index, N element) {
        setAsParentNodeOf(element);
        innerList.set(index, element);
        return this;
    }

    public NodeList<N> remove(int index) {
        innerList.remove(index);
        return this;
    }

    public boolean isEmpty() {
        return innerList.isEmpty();
    }

    public void sort(Comparator<? super N> comparator) {
        Collections.sort(innerList, comparator);
    }

    public void addAll(NodeList<N> otherList) {
        for (N node : otherList) {
            add(node);
        }
    }

    public NodeList<N> add(int index, N node) {
        own(node);
        innerList.add(index, node);
        return this;
    }

    @Override
    public Optional<Node> getParentNode() {
        return Optional.ofNullable(parentNode);
    }

    /**
     * Sets the parentNode
     * 
     * @param parentNode the parentNode
     * @return this, the NodeList
     */
    @Override
    public NodeList<N> setParentNode(Node parentNode) {
        this.parentNode = parentNode;
        setAsParentNodeOf(innerList);
        return this;
    }

    @Override
    public Node getParentNodeForChildren() {
        return parentNode;
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

}
