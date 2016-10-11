package com.github.javaparser.ast;

import com.github.javaparser.Range;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.*;
import java.util.stream.Stream;

/**
 * A node that is a list of nodes.
 * @param <N> the type of nodes contained.
 */
public class NodeList<N extends Node> extends Node implements Iterable<N> {
    private List<N> innerList = new ArrayList<>(0);

    public NodeList() {
        this(Range.UNKNOWN, null);
    }

    public NodeList(Node parent) {
        this(Range.UNKNOWN, parent);
    }

    public NodeList(Range range, Node parent) {
        super(range);
        setParentNode(parent);
    }

    public NodeList<N> add(N node) {
        setAsParentNodeOf(node);
        innerList.add(node);
        return this;
    }

    public NodeList<N> remove(N node) {
        innerList.remove(node);
        node.setParentNode(null);
        return this;
    }

    public static <X extends Node> NodeList<X> nodeList(X... nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        for(X node: nodes) {
            nodeList.add(node);
        }
        return nodeList;
    }

    public static <X extends Node> NodeList<X> nodeList(Collection<X> nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        nodeList.innerList.addAll(nodes);
        return nodeList;
    }

    public static <X extends Node> NodeList<X> nodeList(NodeList<X> nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        nodeList.innerList.addAll(nodes.innerList);
        return nodeList;
    }

    public boolean contains(N node) {
        return innerList.contains(node);
    }

    public Stream<N> stream() {
        return innerList.stream();
    }

    @Override public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
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

    public void addAll(NodeList<N> annotations) {
        innerList.addAll(annotations.innerList);
    }

    public static <X extends Node> NodeList<X> emptyNodeList() {
        return new NodeList<X>();
    }
}
