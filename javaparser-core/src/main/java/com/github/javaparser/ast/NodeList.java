package com.github.javaparser.ast;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Optional;
import java.util.Spliterator;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

import com.github.javaparser.HasParentNode;
import com.github.javaparser.ast.observing.AstObserver;
import com.github.javaparser.ast.observing.Observable;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.visitor.VoidVisitor;

/**
 * A list of nodes.
 *
 * @param <N> the type of nodes contained.
 */
public class NodeList<N extends Node>
        implements List<N>, Iterable<N>, HasParentNode<NodeList<N>>, Visitable, Observable {
    private List<N> innerList = new ArrayList<>(0);

    private Node parentNode;

    private List<AstObserver> observers = new ArrayList<>();

    public NodeList() {
        this(null);
    }

    public NodeList(Node parent) {
        setParentNode(parent);
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
        notifyElementRemoved(innerList.indexOf(node), node);
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

    @Override
    public Stream<N> stream() {
        return innerList.stream();
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
        setAsParentNodeOf(element);
        // TODO notify
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
        Collections.sort(innerList, comparator);
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
     * @param action
     * @see java.lang.Iterable#forEach(java.util.function.Consumer)
     */
    @Override
    public void forEach(Consumer<? super N> action) {
        innerList.forEach(action);
    }

    /**
     * @param o
     * @return
     * @see java.util.List#contains(java.lang.Object)
     */
    @Override
    public boolean contains(Object o) {
        return innerList.contains(o);
    }

    /**
     * @return
     * @see java.util.List#toArray()
     */
    @Override
    public Object[] toArray() {
        return innerList.toArray();
    }

    /**
     * @param a
     * @return
     * @see java.util.List#toArray(java.lang.Object[])
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return innerList.toArray(a);
    }

    /**
     * @param o
     * @return
     * @see java.util.List#remove(java.lang.Object)
     */
    @Override
    public boolean remove(Object o) {
        int indexOf = innerList.indexOf(o);
        if (indexOf != -1)
            notifyElementRemoved(indexOf, (Node) o);
        boolean remove = innerList.remove(o);
        if (o != null && o instanceof Node)
            ((Node) o).setParentNode(null);
        return remove;
    }

    /**
     * @param c
     * @return
     * @see java.util.List#containsAll(java.util.Collection)
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return innerList.containsAll(c);
    }

    /**
     * @param c
     * @return
     * @see java.util.List#addAll(java.util.Collection)
     */
    @Override
    public boolean addAll(Collection<? extends N> c) {
        for (N n : c)
            own(n);
        // TODO notify
        return innerList.addAll(c);
    }

    /**
     * @param index
     * @param c
     * @return
     * @see java.util.List#addAll(int, java.util.Collection)
     */
    @Override
    public boolean addAll(int index, Collection<? extends N> c) {
        for (N n : c)
            own(n);
        // TODO notify
        return innerList.addAll(index, c);
    }

    /**
     * @param c
     * @return
     * @see java.util.List#removeAll(java.util.Collection)
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        // TODO notify
        boolean removeAll = innerList.removeAll(c);
        for (Object o : c) {
            if (o != null && o instanceof Node)
                ((Node) o).setParentNode(null);
        }
        return removeAll;
    }

    /**
     * @param c
     * @return
     * @see java.util.List#retainAll(java.util.Collection)
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        // TODO notify
        return innerList.retainAll(c);
    }

    /**
     * @param operator
     * @see java.util.List#replaceAll(java.util.function.UnaryOperator)
     */
    @Override
    public void replaceAll(UnaryOperator<N> operator) {
        // TODO notify
        innerList.replaceAll(operator);
    }

    /**
     * @param filter
     * @return
     * @see java.util.Collection#removeIf(java.util.function.Predicate)
     */
    @Override
    public boolean removeIf(Predicate<? super N> filter) {
        boolean atLeastOneRemoved = false;
        Iterator<N> iterator = innerList.iterator();
        while (iterator.hasNext()) {
            N next = iterator.next();
            if (filter.test(next)) {
                if (next != null)
                    next.setParentNode(null);
                notifyElementRemoved(innerList.indexOf(next), next);
                atLeastOneRemoved = true;
                iterator.remove();
            }
        }
        return atLeastOneRemoved;
    }

    /**
     * 
     * @see java.util.List#clear()
     */
    @Override
    public void clear() {
        // TODO notify
        for (Node n : innerList)
            n.setParentNode(null);
        innerList.clear();
    }

    /**
     * @param o
     * @return
     * @see java.util.List#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        return innerList.equals(o);
    }

    /**
     * @return
     * @see java.util.List#hashCode()
     */
    @Override
    public int hashCode() {
        return innerList.hashCode();
    }

    /**
     * @param o
     * @return
     * @see java.util.List#indexOf(java.lang.Object)
     */
    @Override
    public int indexOf(Object o) {
        return innerList.indexOf(o);
    }

    /**
     * @param o
     * @return
     * @see java.util.List#lastIndexOf(java.lang.Object)
     */
    @Override
    public int lastIndexOf(Object o) {
        return innerList.lastIndexOf(o);
    }

    /**
     * @return
     * @see java.util.List#listIterator()
     */
    @Override
    public ListIterator<N> listIterator() {
        return innerList.listIterator();
    }

    /**
     * @param index
     * @return
     * @see java.util.List#listIterator(int)
     */
    @Override
    public ListIterator<N> listIterator(int index) {
        return innerList.listIterator(index);
    }

    /**
     * @return
     * @see java.util.Collection#parallelStream()
     */
    @Override
    public Stream<N> parallelStream() {
        return innerList.parallelStream();
    }

    /**
     * @param fromIndex
     * @param toIndex
     * @return
     * @see java.util.List#subList(int, int)
     */
    @Override
    public List<N> subList(int fromIndex, int toIndex) {
        return innerList.subList(fromIndex, toIndex);
    }

    /**
     * @return
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

    @Override
    public void unregister(AstObserver observer) {
        this.observers.remove(observer);
    }

    @Override
    public void register(AstObserver observer) {
        this.observers.add(observer);
    }

    @Override
    public boolean isRegistered(AstObserver observer) {
        return this.observers.contains(observer);
    }

}
