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
import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.EqualsVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.printer.PrettyPrinter;
import com.github.javaparser.printer.PrettyPrinterConfiguration;

import java.lang.reflect.Field;
import java.util.*;

import static java.util.Collections.unmodifiableList;

/**
 * Abstract class for all nodes of the AST.
 *
 * Each Node can have one associated comment which describe it and
 * a number of "orphan comments" which it contains but are not specifically
 * associated to any element.
 * 
 * @author Julio Vilmar Gesser
 */
// Use <Node> to prevent Node from becoming generic.
public abstract class Node implements Cloneable, HasParentNode<Node>, Visitable {
    /**
     * This can be used to sort nodes on position.
     */
    public static Comparator<Node> NODE_BY_BEGIN_POSITION = (a, b) -> {
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

    private Range range;

    private Node parentNode;

    private List<Node> childrenNodes = new LinkedList<>();
    private List<Comment> orphanComments = new LinkedList<>();

    private IdentityHashMap<UserDataKey<?>, Object> userData = null;

    private Comment comment;

    public Node(Range range) {
        this.range = range;
    }
    
    /**
     * This is a comment associated with this node.
     *
     * @return comment property
     */
    public final Comment getComment() {
        return comment;
    }

    /**
     * The begin position of this node in the source file.
     */
    public Optional<Position> getBegin() {
        if (range == null) {
            return Optional.empty();
        }
        return Optional.of(range.begin);
    }

    /**
     * The end position of this node in the source file.
     */
    public Optional<Position> getEnd() {
        if (range == null) {
            return Optional.empty();
        }
        return Optional.of(range.end);
    }

    /**
     * Sets the begin position of this node in the source file.
     */
    public Node setBegin(Position begin) {
        if (range == null) {
            range = Range.range(0, 0, 0, 0);
        }
        range = range.withBegin(begin);
        return this;
    }

    /**
     * Sets the end position of this node in the source file.
     */
    public Node setEnd(Position end) {
        if (range == null) {
            range = Range.range(0, 0, 0, 0);
        }
        range = range.withEnd(end);
        return this;
    }

    /**
     * @return the range of characters in the source code that this node covers.
     */
    public Optional<Range> getRange() {
        return Optional.ofNullable(range);
    }

    /**
     * @param range the range of characters in the source code that this node covers.
     * null can be used to indicate that no range information is known,
     * or that it is not of interest. 
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
    public final Node setComment(final Comment comment) {
        if (comment != null && (this instanceof Comment)) {
            throw new RuntimeException("A comment can not be commented");
        }
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
        return (Node) accept(new CloneVisitor(), null);
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
        return unmodifiableList(childrenNodes);
    }

    public <N extends Node> boolean containsWithin(N other) {
        if (getRange().isPresent() && other.getRange().isPresent()) {
            return range.contains(other.getRange().get());
        }
        return false;
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

        for (Node child : getChildNodes()) {
            if (child.getComment() != null) {
                comments.add(child.getComment());
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
    @Override
    public Node setParentNode(Node parentNode) {
        // remove from old parent, if any
        if (this.parentNode != null) {
            this.parentNode.childrenNodes.remove(this);
        }
        this.parentNode = parentNode;
        // add to new parent, if any
        if (this.parentNode != null) {
            this.parentNode.childrenNodes.add(this);
        }
        return this;
    }

    public static final int ABSOLUTE_BEGIN_LINE = -1;
    public static final int ABSOLUTE_END_LINE = -2;

    @Deprecated
    public boolean isPositionedAfter(Position position) {
        if (range == null) {
            return false;
        }
        return range.isAfter(position);
    }

    @Deprecated
    public boolean isPositionedBefore(Position position) {
        if (range == null) {
            return true;
        }
        return range.isBefore(position);
    }

    public boolean hasComment() {
        return comment != null;
    }

    public void tryAddImportToParentCompilationUnit(Class<?> clazz) {
        CompilationUnit parentNode = getAncestorOfType(CompilationUnit.class);
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
        for (Node child : getChildNodes()) {
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

    @Override
    public Node getParentNodeForChildren() {
        return this;
    }

    protected void setAsParentNodeOf(NodeList<? extends Node> list) {
        if (list != null) {
            list.setParentNode(getParentNodeForChildren());
        }
    }
}
