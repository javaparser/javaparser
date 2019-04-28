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

package com.github.javaparser.ast;

import com.github.javaparser.HasParentNode;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.Observable;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.InternalProperty;

import java.util.*;
import java.util.function.*;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * A list of nodes.
 * It usually has a parent node.
 * Unlike normal Nodes, this does not mean that it is a child of that parent.
 * Instead, this list will make every node it contains a child of its parent.
 * This way, a NodeList does not create an extra level inside the AST.
 *
 * @param <N> the type of nodes contained.
 */
public class NodeList<N extends Node> implements List<N>, Iterable<N>, HasParentNode<NodeList<N>>, Visitable, Observable {
    @InternalProperty
    private List<N> innerList = new ArrayList<>(0);

    private Node parentNode;

    private List<AstObserver> observers = new ArrayList<>();

    public NodeList() {
        parentNode = null;
    }

    public NodeList(Collection<N> n) {
        this.addAll(n);
    }

    @SafeVarargs
    public NodeList(N... n) {
        this.addAll(Arrays.asList(n));
    }

    @Override
    public boolean add(N node) {
        notifyElementAdded(innerList.size(), node);
        own(node);
        return innerList.add(node);
    }

    private void own(N node) {
        if (node == null) {
            return;
        }
        setAsParentNodeOf(node);
    }

    public boolean remove(Node node) {
        int index = innerList.indexOf(node);
        if (index != -1) {
            notifyElementRemoved(index, node);
            node.setParentNode(null);
        }
        return innerList.remove(node);
    }

    public N removeFirst() {
        return remove(0);
    }

    public N removeLast() {
        return remove(innerList.size() - 1);
    }

    @SafeVarargs
    public static <X extends Node> NodeList<X> nodeList(X... nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        Collections.addAll(nodeList, nodes);
        return nodeList;
    }

    public static <X extends Node> NodeList<X> nodeList(Collection<X> nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        nodeList.addAll(nodes);
        return nodeList;
    }

    public static <X extends Node> NodeList<X> nodeList(NodeList<X> nodes) {
        final NodeList<X> nodeList = new NodeList<>();
        nodeList.addAll(nodes);
        return nodeList;
    }

    public boolean contains(N node) {
        return innerList.contains(node);
    }

    @Override
    public int size() {
        return innerList.size();
    }

    @Override
    public N get(int i) {
        return innerList.get(i);
    }

    @Override
    public Iterator<N> iterator() {
        // TODO take care of "Iterator.remove"
        return innerList.iterator();
    }

    @Override
    public N set(int index, N element) {
        if (index < 0 || index >= innerList.size()) {
            throw new IllegalArgumentException("Illegal index. The index should be between 0 and " + innerList.size()
                    + " excluded. It is instead " + index);
        }
        if (element == innerList.get(index)) {
            return element;
        }
        notifyElementReplaced(index, element);
        innerList.get(index).setParentNode(null);
        setAsParentNodeOf(element);
        return innerList.set(index, element);
    }

    @Override
    public N remove(int index) {
        notifyElementRemoved(index, innerList.get(index));
        N remove = innerList.remove(index);
        if (remove != null)
            remove.setParentNode(null);
        return remove;
    }

    @Override
    public boolean isEmpty() {
        return innerList.isEmpty();
    }

    @Override
    public void sort(Comparator<? super N> comparator) {
        innerList.sort(comparator);
    }

    public void addAll(NodeList<N> otherList) {
        for (N node : otherList) {
            add(node);
        }
    }

    @Override
    public void add(int index, N node) {
        notifyElementAdded(index, node);
        own(node);
        innerList.add(index, node);
    }

    /**
     * Inserts the node before all other nodes.
     */
    public NodeList<N> addFirst(N node) {
        add(0, node);
        return this;
    }

    /**
     * Inserts the node after all other nodes. (This is simply an alias for add.)
     */
    public NodeList<N> addLast(N node) {
        add(node);
        return this;
    }

    /**
     * Inserts the node after afterThisNode.
     *
     * @throws IllegalArgumentException when afterThisNode is not in this list.
     */
    public NodeList<N> addAfter(N node, N afterThisNode) {
        int i = indexOf(afterThisNode);
        if (i == -1) {
            throw new IllegalArgumentException("Can't find node to insert after.");
        }
        add(i + 1, node);
        return this;
    }

    /**
     * Inserts the node before beforeThisNode.
     *
     * @throws IllegalArgumentException when beforeThisNode is not in this list.
     */
    public NodeList<N> addBefore(N node, N beforeThisNode) {
        int i = indexOf(beforeThisNode);
        if (i == -1) {
            throw new IllegalArgumentException("Can't find node to insert before.");
        }
        add(i, node);
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

    /**
     * @see java.lang.Iterable#forEach(java.util.function.Consumer)
     */
    @Override
    public void forEach(Consumer<? super N> action) {
        innerList.forEach(action);
    }

    /**
     * @see java.util.List#contains(java.lang.Object)
     */
    @Override
    public boolean contains(Object o) {
        return innerList.contains(o);
    }

    /**
     * @see java.util.List#toArray()
     */
    @Override
    public Object[] toArray() {
        return innerList.toArray();
    }

    /**
     * @see java.util.List#toArray(java.lang.Object[])
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return innerList.toArray(a);
    }

    /**
     * @see java.util.List#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        if (o instanceof Node) {
            return remove((Node) o);
        } else {
            return false;
        }
    }

    /**
     * @see java.util.List#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return innerList.containsAll(c);
    }

    /**
     * @see java.util.List#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends N> c) {
        c.forEach(this::add);
        return !c.isEmpty();
    }

    /**
     * @see java.util.List#addAll(int, java.util.Collection)
     */
    @Override
    public boolean addAll(int index, Collection<? extends N> c) {
        for (N e : c) {
            add(index++, e);
        }
        return !c.isEmpty();
    }

    /**
     * @see java.util.List#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        boolean changed = false;
        for (Object e : c) {
            changed = remove(e) || changed;
        }
        return changed;
    }

    /**
     * @see java.util.List#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        boolean changed = false;
        for (Object e : this.stream().filter(it -> !c.contains(it)).toArray()) {
            if (!c.contains(e)) {
                changed = remove(e) || changed;
            }
        }
        return changed;
    }

    /**
     * @see java.util.List#replaceAll(java.util.function.UnaryOperator)
     */
    @Override
    public void replaceAll(UnaryOperator<N> operator) {
        for (int i = 0; i < this.size(); i++) {
            set(i, operator.apply(this.get(i)));
        }
    }

    /**
     * @see java.util.Collection#removeIf(java.util.function.Predicate)
     */
    @Override
    public boolean removeIf(Predicate<? super N> filter) {
        boolean changed = false;
        for (Object e : this.stream().filter(filter).toArray()) {
            changed = remove(e) || changed;
        }
        return changed;
    }

    /**
     * @see java.util.List#clear()
     */
    @Override
    public void clear() {
        while (!isEmpty()) {
            remove(0);
        }
    }

    /**
     * @see java.util.List#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        return innerList.equals(o);
    }

    /**
     * @see java.util.List#hashCode()
     */
    @Override
    public int hashCode() {
        return innerList.hashCode();
    }

    /**
     * @see java.util.List#indexOf(java.lang.Object)
     */
    @Override
    public int indexOf(Object o) {
        return innerList.indexOf(o);
    }

    /**
     * @see java.util.List#lastIndexOf(java.lang.Object)
     */
    @Override
    public int lastIndexOf(Object o) {
        return innerList.lastIndexOf(o);
    }

    /**
     * @see java.util.List#listIterator()
     */
    @Override
    public ListIterator<N> listIterator() {
        return innerList.listIterator();
    }

    /**
     * @see java.util.List#listIterator(int)
     */
    @Override
    public ListIterator<N> listIterator(int index) {
        return innerList.listIterator(index);
    }

    /**
     * @see java.util.Collection#parallelStream()
     */
    @Override
    public Stream<N> parallelStream() {
        return innerList.parallelStream();
    }

    /**
     * @see java.util.List#subList(int, int)
     */
    @Override
    public List<N> subList(int fromIndex, int toIndex) {
        return innerList.subList(fromIndex, toIndex);
    }

    /**
     * @see java.util.List#spliterator()
     */
    @Override
    public Spliterator<N> spliterator() {
        return innerList.spliterator();
    }

    private void notifyElementAdded(int index, Node nodeAddedOrRemoved) {
        this.observers.forEach(o -> o.listChange(this, AstObserver.ListChangeType.ADDITION, index, nodeAddedOrRemoved));
    }

    private void notifyElementRemoved(int index, Node nodeAddedOrRemoved) {
        this.observers.forEach(o -> o.listChange(this, AstObserver.ListChangeType.REMOVAL, index, nodeAddedOrRemoved));
    }

    private void notifyElementReplaced(int index, Node nodeAddedOrRemoved) {
        this.observers.forEach(o -> o.listReplacement(this, index, this.get(index), nodeAddedOrRemoved));
    }

    @Override
    public void unregister(AstObserver observer) {
        this.observers.remove(observer);
    }

    @Override
    public void register(AstObserver observer) {
        if(!this.observers.contains(observer)) {
            this.observers.add(observer);
        }
    }

    @Override
    public boolean isRegistered(AstObserver observer) {
        return this.observers.contains(observer);
    }

    /**
     * Replaces the first node that is equal to "old" with "replacement".
     *
     * @return true if a replacement has happened.
     */
    public boolean replace(N old, N replacement) {
        int i = indexOf(old);
        if (i == -1) {
            return false;
        }
        set(i, replacement);
        return true;
    }

    /**
     * @return the opposite of isEmpty()
     */
    public boolean isNonEmpty() {
        return !isEmpty();
    }

    public void ifNonEmpty(Consumer<? super NodeList<N>> consumer) {
        if (isNonEmpty())
            consumer.accept(this);
    }

    public static <T extends Node> Collector<T, NodeList<T>, NodeList<T>> toNodeList() {
        return Collector.of(NodeList::new, NodeList::add, (left, right) -> {
            left.addAll(right);
            return left;
        });
    }

    private void setAsParentNodeOf(List<? extends Node> childNodes) {
        if (childNodes != null) {
            for (HasParentNode current : childNodes) {
                current.setParentNode(getParentNodeForChildren());
            }
        }
    }

    private void setAsParentNodeOf(Node childNode) {
        if (childNode != null) {
            childNode.setParentNode(getParentNodeForChildren());
        }
    }

    @Override
    public String toString() {
        return innerList.stream().map(Node::toString).collect(Collectors.joining(", ", "[", "]"));
    }
}
