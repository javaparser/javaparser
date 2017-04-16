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
import com.github.javaparser.Range;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.nodeTypes.NodeWithRange;
import com.github.javaparser.ast.observer.AstObserver;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.observer.PropagatingAstObserver;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import com.github.javaparser.ast.visitor.HashCodeVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.metamodel.InternalProperty;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import com.github.javaparser.metamodel.NodeMetaModel;
import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.printer.PrettyPrinterConfiguration;
import java.util.*;
import static java.util.Collections.unmodifiableList;

/**
 * Base class for all nodes of the abstract syntax tree.
 * <h2>Construction</h2>
 * <p>The tree is built by instantiating the required nodes, then adding them to other nodes.
 * If it is the parser who is building the tree, it will use the largest constructor,
 * the one with "range" as the first parameter.
 * If you want to manually instantiate nodes, we suggest to...
 * <ul>
 * <li>use a convenience method, like "addStatement(...)", or if none are available...</li>
 * <li>use a convenient constructor, like ClassOrInterfaceType(String name), or if none are available...</li>
 * <li>use the default constructor.</li>
 * <li>Alternatively, use one of the JavaParser.parse(snippet) methods.</li>
 * </ul>
 * ... and use the various methods on the node to initialize it further, if needed.
 * <h2>Parent/child</h2>
 * <p>The parent node field is managed automatically and can be seen as read only.
 * Note that there is only one parent,
 * and trying to use the same node in two places will lead to unexpected behaviour.
 * It is advised to clone() a node before moving it around.
 * <h2>Comments</h2>
 * <p>Each Node can have one associated comment which describes it and
 * a number of "orphan comments" which it contains but are not specifically
 * associated to any child.
 * <h2>Positions</h2>
 * <p>When the parser creates nodes, it sets their source code position in the "range" field.
 * When you manually instantiate nodes, their range is not set.
 * The top left character is position 1, 1.
 * Note that since this is an <i>abstract</i> syntax tree,
 * it leaves out a lot of text from the original source file,
 * like where braces or comma's are exactly.
 * Therefore there is no position information on everything in the original source file.
 * <h2>Observers</h2>
 * <p>It is possible to add observers to the the tree.
 * Any change in the tree is sent as an event to any observers watching.
 * <h2>Visitors</h2>
 * <p>The most comfortable way of working with an abstract syntax tree is using visitors.
 * You can use one of the visitors in the visitor package, or extend one of them.
 * A visitor can be "run" by calling accept on a node:
 * <pre>node.accept(visitor, argument);</pre>
 * where argument is an object of your choice (often simply null.)
 *
 * @author Julio Vilmar Gesser
 */
public abstract class Node implements Cloneable, HasParentNode<Node>, Visitable, NodeWithRange<Node> {

    /**
     * Different registration mode for observers on nodes.
     */
    public enum ObserverRegistrationMode {

        /**
         * Notify exclusively for changes happening on this node alone.
         */
        JUST_THIS_NODE, /**
         * Notify for changes happening on this node and all its descendants existing at the moment in
         * which the observer was registered. Nodes attached later will not be observed.
         */
        THIS_NODE_AND_EXISTING_DESCENDANTS, /**
         * Notify for changes happening on this node and all its descendants. The descendants existing at the moment in
         * which the observer was registered will be observed immediately. As new nodes are attached later they are
         * automatically registered to be observed.
         */
        SELF_PROPAGATING
    }

    /**
     * This can be used to sort nodes on position.
     */
    public static Comparator<NodeWithRange<?>> NODE_BY_BEGIN_POSITION = (a, b) -> {
        if (a.getRange().isPresent() && b.getRange().isPresent()) {
            return a.getRange().get().begin.compareTo(b.getRange().get().begin);
        }
        if (a.getRange().isPresent() || b.getRange().isPresent()) {
            if (a.getRange().isPresent()) {
                return 1;
            }
            return -1;
        }
        return 0;
    };

    private static final PrettyPrinter toStringPrinter = new PrettyPrinter(new PrettyPrinterConfiguration());

    protected static final PrettyPrinterConfiguration prettyPrinterNoCommentsConfiguration = new PrettyPrinterConfiguration().setPrintComments(false);

    @InternalProperty
    private Range range;

    @InternalProperty
    private Node parentNode;

    @InternalProperty
    private List<Node> childNodes = new LinkedList<>();

    @InternalProperty
    private List<Comment> orphanComments = new LinkedList<>();

    @InternalProperty
    private IdentityHashMap<DataKey<?>, Object> data = null;

    private Comment comment;

    @InternalProperty
    private List<AstObserver> observers = new ArrayList<>();

    public Node(Range range) {
        this.range = range;
    }

    /**
     * This is a comment associated with this node.
     *
     * @return comment property
     */
    public final Optional<Comment> getComment() {
        return Optional.ofNullable(comment);
    }

    /**
     * @return the range of characters in the source code that this node covers.
     */
    public Optional<Range> getRange() {
        return Optional.ofNullable(range);
    }

    /**
     * @param range the range of characters in the source code that this node covers. null can be used to indicate that
     * no range information is known, or that it is not of interest.
     */
    public Node setRange(Range range) {
        if (this.range == range) {
            return this;
        }
        notifyPropertyChange(ObservableProperty.RANGE, this.range, range);
        this.range = range;
        return this;
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setComment(final Comment comment) {
        if (this.comment == comment) {
            return this;
        }
        if (comment != null && (this instanceof Comment)) {
            throw new RuntimeException("A comment can not be commented");
        }
        notifyPropertyChange(ObservableProperty.COMMENT, this.comment, comment);
        if (this.comment != null) {
            this.comment.setCommentedNode(null);
        }
        this.comment = comment;
        if (comment != null) {
            this.comment.setCommentedNode(this);
        }
        return this;
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setLineComment(String comment) {
        return setComment(new LineComment(comment));
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setBlockComment(String comment) {
        return setComment(new BlockComment(comment));
    }

    /**
     * Return the String representation of this node.
     *
     * @return the String representation of this node
     */
    @Override
    public final String toString() {
        return toStringPrinter.print(this);
    }

    public final String toString(PrettyPrinterConfiguration prettyPrinterConfiguration) {
        return new PrettyPrinter(prettyPrinterConfiguration).print(this);
    }

    @Override
    public final int hashCode() {
        return HashCodeVisitor.hashCode(this);
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj == null || !(obj instanceof Node)) {
            return false;
        }
        return EqualsVisitor.equals(this, (Node) obj);
    }

    @Override
    public Optional<Node> getParentNode() {
        return Optional.ofNullable(parentNode);
    }

    /**
     * Contains all nodes that have this node set as their parent.
     * You can add nodes to it by setting a node's parent to this node.
     * You can remove nodes from it by setting a child node's parent to something other than this node.
     *
     * @return all nodes that have this node as their parent.
     */
    public List<Node> getChildNodes() {
        return unmodifiableList(childNodes);
    }

    public void addOrphanComment(Comment comment) {
        orphanComments.add(comment);
        comment.setParentNode(this);
    }

    public boolean removeOrphanComment(Comment comment) {
        boolean removed = orphanComments.remove(comment);
        if (removed) {
            comment.setParentNode(null);
        }
        return removed;
    }

    /**
     * This is a list of Comment which are inside the node and are not associated
     * with any meaningful AST Node.
     * <p>
     * For example, comments at the end of methods (immediately before the parenthesis)
     * or at the end of CompilationUnit are orphan comments.
     * <p>
     * When more than one comment preceeds a statement, the one immediately preceding it
     * it is associated with the statements, while the others are orphans.
     * <p>
     * Changes to this list are not persisted.
     *
     * @return all comments that cannot be attributed to a concept
     */
    public List<Comment> getOrphanComments() {
        return new LinkedList<>(orphanComments);
    }

    /**
     * This is the list of Comment which are contained in the Node either because
     * they are properly associated to one of its children or because they are floating
     * around inside the Node
     *
     * @return all Comments within the node as a list
     */
    public List<Comment> getAllContainedComments() {
        List<Comment> comments = new LinkedList<>();
        comments.addAll(getOrphanComments());
        for (Node child : getChildNodes()) {
            child.getComment().ifPresent(comments::add);
            comments.addAll(child.getAllContainedComments());
        }
        return comments;
    }

    /**
     * Assign a new parent to this node, removing it
     * from the list of children of the previous parent, if any.
     *
     * @param parentNode node to be set as parent
     */
    @Override
    public Node setParentNode(Node parentNode) {
        if (parentNode == this.parentNode) {
            return this;
        }
        observers.forEach(o -> o.parentChange(this, this.parentNode, parentNode));
        // remove from old parent, if any
        if (this.parentNode != null) {
            this.parentNode.childNodes.remove(this);
        }
        this.parentNode = parentNode;
        // add to new parent, if any
        if (this.parentNode != null) {
            this.parentNode.childNodes.add(this);
        }
        return this;
    }

    public static final int ABSOLUTE_BEGIN_LINE = -1;

    public static final int ABSOLUTE_END_LINE = -2;

    /** @deprecated use getComment().isPresent() */
    @Deprecated
    public boolean hasComment() {
        return comment != null;
    }

    public void tryAddImportToParentCompilationUnit(Class<?> clazz) {
        getAncestorOfType(CompilationUnit.class).ifPresent(p -> p.addImport(clazz));
    }

    /**
     * Recursively finds all nodes of a certain type.
     *
     * @param clazz the type of node to find.
     */
    public <N extends Node> List<N> getChildNodesByType(Class<N> clazz) {
        List<N> nodes = new ArrayList<>();
        for (Node child : getChildNodes()) {
            if (clazz.isInstance(child)) {
                nodes.add(clazz.cast(child));
            }
            nodes.addAll(child.getNodesByType(clazz));
        }
        return nodes;
    }

    /**
     * @deprecated use getChildNodesByType
     */
    @Deprecated
    public <N extends Node> List<N> getNodesByType(Class<N> clazz) {
        return getChildNodesByType(clazz);
    }

    /**
     * Gets data for this component using the given key.
     *
     * @param <M> The type of the data.
     * @param key The key for the data
     * @return The data or null of no data was found for the given key
     * @see DataKey
     */
    @SuppressWarnings("unchecked")
    public <M> M getData(final DataKey<M> key) {
        if (data == null) {
            return null;
        }
        return (M) data.get(key);
    }

    /**
     * Sets data for this component using the given key.
     * For information on creating DataKey, see {@link DataKey}.
     *
     * @param <M> The type of data
     * @param key The singleton key for the data
     * @param object The data object
     * @see DataKey
     */
    public <M> void setData(DataKey<M> key, M object) {
        if (data == null) {
            data = new IdentityHashMap<>();
        }
        data.put(key, object);
    }

    /**
     * Try to remove this node from the parent
     *
     * @return true if removed, false otherwise
     * @throws RuntimeException if it fails in an unexpected way
     */
    public boolean remove() {
        if (parentNode == null) {
            return false;
        }
        return parentNode.remove(this);
    }

    @Override
    public Node getParentNodeForChildren() {
        return this;
    }

    protected void setAsParentNodeOf(NodeList<? extends Node> list) {
        if (list != null) {
            list.setParentNode(getParentNodeForChildren());
        }
    }

    public <P> void notifyPropertyChange(ObservableProperty property, P oldValue, P newValue) {
        this.observers.forEach(o -> o.propertyChange(this, property, oldValue, newValue));
    }

    @Override
    public void unregister(AstObserver observer) {
        this.observers.remove(observer);
    }

    @Override
    public void register(AstObserver observer) {
        this.observers.add(observer);
    }

    /**
     * Register a new observer for the given node. Depending on the mode specified also descendants, existing
     * and new, could be observed. For more details see <i>ObserverRegistrationMode</i>.
     */
    public void register(AstObserver observer, ObserverRegistrationMode mode) {
        if (mode == null) {
            throw new IllegalArgumentException("Mode should be not null");
        }
        switch(mode) {
            case JUST_THIS_NODE:
                register(observer);
                break;
            case THIS_NODE_AND_EXISTING_DESCENDANTS:
                registerForSubtree(observer);
                break;
            case SELF_PROPAGATING:
                registerForSubtree(PropagatingAstObserver.transformInPropagatingObserver(observer));
                break;
            default:
                throw new UnsupportedOperationException("This mode is not supported: " + mode);
        }
    }

    /**
     * Register the observer for the current node and all the contained node and nodelists, recursively.
     */
    public void registerForSubtree(AstObserver observer) {
        register(observer);
        this.getChildNodes().forEach(c -> c.registerForSubtree(observer));
        this.getNodeLists().forEach(nl -> {
            if (nl != null)
                nl.register(observer);
        });
    }

    @Override
    public boolean isRegistered(AstObserver observer) {
        return this.observers.contains(observer);
    }

    /**
     * The list of NodeLists owned by this node.
     */
    public List<NodeList<?>> getNodeLists() {
        return Collections.emptyList();
    }

    public boolean remove(Node node) {
        if (node == null)
            return false;
        if (comment != null) {
            if (node == comment) {
                removeComment();
                return true;
            }
        }
        return false;
    }

    public Node removeComment() {
        return setComment((Comment) null);
    }

    @Override
    public Node clone() {
        return (Node) accept(new CloneVisitor(), null);
    }

    public NodeMetaModel getMetaModel() {
        return JavaParserMetaModel.nodeMetaModel;
    }
}
