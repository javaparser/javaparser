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

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.visitor.*;
import com.github.javaparser.utils.PositionUtils;

import java.util.*;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static com.github.javaparser.utils.Utils.none;
import static com.github.javaparser.utils.Utils.some;
import static java.util.Collections.*;

/**
 * Abstract class for all nodes of the AST.
 *
 * Each Node can have one associated comment which describe it and
 * a number of "orphan comments" which it contains but are not specifically
 * associated to any element.
 * 
 * @author Julio Vilmar Gesser
 */
public abstract class Node implements Cloneable {
    /**
     * This can be used to sort nodes on position.
     */
    public static Comparator<Node> NODE_BY_BEGIN_POSITION = (a, b) -> a.getBegin().compareTo(b.getBegin());

    private Range range;

    private Node parentNode;

    private List<Node> childrenNodes = new LinkedList<>();
    private List<Comment> orphanComments = new LinkedList<>();

    private IdentityHashMap<UserDataKey<?>, Object> userData = null;

    private Optional<? extends Comment> comment = none();

    public Node(Range range) {
        this.range = range;
    }

    /**
     * Accept method for visitor support.
     * 
     * @param <R>
     *            the type the return value of the visitor
     * @param <A>
     *            the type the argument passed to the visitor
     * @param v
     *            the visitor implementation
     * @param arg
     *            the argument passed to the visitor
     * @return the result of the visit
     */
    public abstract <R, A> R accept(GenericVisitor<R, A> v, A arg);

    /**
     * Accept method for visitor support.
     * 
     * @param <A>
     *            the type the argument passed for the visitor
     * @param v
     *            the visitor implementation
     * @param arg
     *            any value relevant for the visitor
     */
    public abstract <A> void accept(VoidVisitor<A> v, A arg);

    /**
     * This is a comment associated with this node.
     *
     * @return comment property
     */
    public Optional<? extends Comment> getComment() {
        return comment;
    }

    /**
     * The begin position of this node in the source file.
     */
    public Position getBegin() {
        return range.begin;
    }

    /**
     * The end position of this node in the source file.
     */
    public Position getEnd() {
        return range.end;
    }

    /**
     * Sets the begin position of this node in the source file.
     */
    public Node setBegin(Position begin) {
        range = range.withBegin(begin);
        return this;
    }

    /**
     * Sets the end position of this node in the source file.
     */
    public Node setEnd(Position end) {
        range = range.withEnd(end);
        return this;
    }

    /**
     * @return the range of characters in the source code that this node covers.
     */
    public Range getRange() {
        return range;
    }

    /**
     * @param range the range of characters in the source code that this node covers.
     */
    public Node setRange(Range range) {
        this.range = range;
        return this;
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setComment(final Optional<? extends Comment> comment) {
        assertNotNull(comment);
        comment.ifPresent(c -> {if (this instanceof Comment) throw new AssertionError("A comment can not be commented");});
        this.comment.ifPresent(c -> c.setCommentedNode(null));
        this.comment = comment;
        this.comment.ifPresent(c -> c.setCommentedNode(this));
        return this;
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setLineComment(String comment) {
        return setComment(some(new LineComment(comment)));
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final Node setBlockComment(String comment) {
        return setComment(some(new BlockComment(comment)));
    }

    /**
     * Return the String representation of this node.
     * 
     * @return the String representation of this node
     */
    @Override
    public final String toString() {
        final DumpVisitor visitor = new DumpVisitor();
        accept(visitor, null);
        return visitor.getSource();
    }

    public final String toStringWithoutComments() {
        final DumpVisitor visitor = new DumpVisitor(false);
        accept(visitor, null);
        return visitor.getSource();
    }

    @Override
    public final int hashCode() {
        return toString().hashCode();
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj == null || !(obj instanceof Node)) {
            return false;
        }
        return EqualsVisitor.equals(this, (Node) obj);
    }

    @Override
    public Node clone() {
        return this.accept(new CloneVisitor(), null);
    }

    public Node getParentNode() {
        return parentNode;
    }

    @SuppressWarnings("unchecked")
    public <T> T getParentNodeOfType(Class<T> classType) {
        Node parent = parentNode;
        while (parent != null) {
            if (classType.isAssignableFrom(parent.getClass()))
                return (T) parent;
            parent = parent.parentNode;
        }
        return null;
    }

    /**
     * Contains all nodes that have this node set as their parent.
     * You can add nodes to it by setting a node's parent to this node.
     * You can remove nodes from it by setting a child node's parent to something other than this node.
     *
     * @return all nodes that have this node as their parent.
     */
    public List<Node> getChildrenNodes() {
        return unmodifiableList(childrenNodes);
    }

    /**
     * Before 3.0.0.alpha-5, if we had a list of nodes, those nodes would not have the list
     * as its parent, but the node containing the list.
     * This method returns the children in that way: there are no lists, and all nodes that are
     * in lists are directly in this list.
     * @deprecated this will be gone in 3.0.0 release.
     */
    @Deprecated
    public List<Node> getBackwardsCompatibleChildrenNodes() {
        List<Node> children = new ArrayList<>();
        for (Node childNode : getChildrenNodes()) {
            // Avoid attributing comments to NodeLists by pretending they don't exist.
            if (childNode instanceof NodeList) {
                for (Node subChildNode : ((NodeList<Node>) childNode)) {
                    children.add(subChildNode);
                }
            } else {
                children.add(childNode);
            }
        }
        PositionUtils.sortByBeginPosition(children);
        return children;
    }

    public <N extends Node> boolean containsWithin(N other) {
        return range.contains(other.getRange());
    }

    public void addOrphanComment(Comment comment) {
        orphanComments.add(comment);
        comment.setParentNode(this);
    }

    /**
     * This is a list of Comment which are inside the node and are not associated
     * with any meaningful AST Node.
     *
     * For example, comments at the end of methods (immediately before the parenthesis)
     * or at the end of CompilationUnit are orphan comments.
     *
     * When more than one comment preceeds a statement, the one immediately preceding it
     * it is associated with the statements, while the others are orphans.
     * 
     * @return all comments that cannot be attributed to a concept
     */
    public List<Comment> getOrphanComments() {
        return orphanComments;
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

        for (Node child : getChildrenNodes()) {
            if (child.getComment().isPresent()) {
                comments.add(child.getComment().get());
            }
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
    public void setParentNode(Node parentNode) {
        // remove from old parent, if any
        if (this.parentNode != null) {
            this.parentNode.childrenNodes.remove(this);
        }
        this.parentNode = parentNode;
        // add to new parent, if any
        if (this.parentNode != null) {
            this.parentNode.childrenNodes.add(this);
        }
    }

    protected void setAsParentNodeOf(List<? extends Node> childNodes) {
        if (childNodes != null) {
            for (Node current : childNodes) {
                current.setParentNode(this);
            }
        }
    }

    protected void setAsParentNodeOf(Node childNode) {
        if (childNode != null) {
            childNode.setParentNode(this);
        }
    }

    protected void setAsParentNodeOf(Optional<? extends Node> childNode) {
        assertNotNull(childNode);
        childNode.ifPresent(c -> c.setParentNode(this));
    }

    public static final int ABSOLUTE_BEGIN_LINE = -1;
    public static final int ABSOLUTE_END_LINE = -2;

    public boolean isPositionedAfter(Position position) {
        return range.isAfter(position);
    }

    public boolean isPositionedBefore(Position position) {
        return range.isBefore(position);
    }

    public void tryAddImportToParentCompilationUnit(Class<?> clazz) {
        CompilationUnit parentNode = getParentNodeOfType(CompilationUnit.class);
        if (parentNode != null) {
            parentNode.addImport(clazz);
        }
    }

    /**
     * Recursively finds all nodes of a certain type.
     *
     * @param clazz the type of node to find.
     */
    public <N extends Node> List<N> getNodesByType(Class<N> clazz) {
        List<N> nodes = new ArrayList<>();
        for (Node child : getChildrenNodes()) {
            if (clazz.isInstance(child)) {
                nodes.add(clazz.cast(child));
            }
            nodes.addAll(child.getNodesByType(clazz));
        }
        return nodes;
    }

    /**
     * Gets user data for this component using the given key.
     *
     * @param <M>
     *            The type of the user data.
     *
     * @param key
     *            The key for the data
     * @return The user data or null of no user data was found for the given key
     * @see UserDataKey
     */
    public <M> M getUserData(final UserDataKey<M> key) {
        if (userData == null) {
            return null;
        }
        return (M) userData.get(key);
    }

    /**
     * Sets user data for this component using the given key.
     * For information on creating UserDataKey, see {@link UserDataKey}.
     *
     * @param <M>
     *            The type of user data
     *
     * @param key
     *            The singleton key for the user data
     * @param object
     *            The user data object
     * @throws IllegalArgumentException
     * @see UserDataKey
     */
    public <M> void setUserData(UserDataKey<M> key, M object) {
        if (userData == null) {
            userData = new IdentityHashMap<>();
        }
        userData.put(key, object);
    }

    /**
     * Try to remove this node from the parent
     * 
     * @return true if removed, false otherwise
     * @throws RuntimeException if it fails in an unexpected way
     */
    public boolean remove() {
        Node parentNode = this.parentNode;
        if (parentNode == null)
            return false;
        boolean success = false;
        Class<?> parentClass = parentNode.getClass();
        while (parentClass != Object.class) {
            for (Field f : parentClass.getDeclaredFields()) {
                f.setAccessible(true);
                try {
                    Object object = f.get(parentNode);
                    if (object == null)
                        continue;
                    if (Collection.class.isAssignableFrom(object.getClass())) {
                        Collection<?> l = (Collection<?>) object;
                        boolean remove = l.remove(this);
                        success |= remove;
                    } else if (NodeList.class.isAssignableFrom(object.getClass())) {
                        NodeList<Node> l = (NodeList<Node>) object;
                        success |= l.remove(this);
                    } else if (Optional.class.equals(f.getType())) {
                        Optional<?> opt = (Optional<?>) object;
                        if (opt.isPresent())
                            if (opt.get() == this)
                                f.set(parentNode, Optional.empty());
                    } else if (object == this) {
                        f.set(parentNode, null);
                        success |= true;
                    }
                } catch (IllegalArgumentException | IllegalAccessException e) {
                    throw new RuntimeException("Error while removing " + getClass().getSimpleName(), e);
                }
            }
            parentClass = parentClass.getSuperclass();
        }
        setParentNode(null);
        return success;
    }
}
