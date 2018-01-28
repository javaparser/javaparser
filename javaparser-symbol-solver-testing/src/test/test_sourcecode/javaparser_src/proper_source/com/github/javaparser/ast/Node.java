/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
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

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.visitor.*;

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

    private int beginLine;

    private int beginColumn;

    private int endLine;

    private int endColumn;

    private Node parentNode;

    private List<Node> childrenNodes = new LinkedList<Node>();
    private List<Comment> orphanComments = new LinkedList<Comment>();

    /**
     * This attribute can store additional information from semantic analysis.
     */
    private Object data;

    private Comment comment;

    public Node() {
    }

    public Node(final int beginLine, final int beginColumn, final int endLine, final int endColumn) {
        this.beginLine = beginLine;
        this.beginColumn = beginColumn;
        this.endLine = endLine;
        this.endColumn = endColumn;
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
     * Return the begin column of this node.
     * 
     * @return the begin column of this node
     */
    public final int getBeginColumn() {
        return beginColumn;
    }

    /**
     * Return the begin line of this node.
     * 
     * @return the begin line of this node
     */
    public final int getBeginLine() {
        return beginLine;
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
     * Use this to retrieve additional information associated to this node.
     *
     * @return data property
     */
    public final Object getData() {
        return data;
    }

    /**
     * Return the end column of this node.
     * 
     * @return the end column of this node
     */
    public final int getEndColumn() {
        return endColumn;
    }

    /**
     * Return the end line of this node.
     * 
     * @return the end line of this node
     */
    public final int getEndLine() {
        return endLine;
    }

    /**
     * Sets the begin column of this node.
     * 
     * @param beginColumn
     *            the begin column of this node
     */
    public final void setBeginColumn(final int beginColumn) {
        this.beginColumn = beginColumn;
    }

    /**
     * Sets the begin line of this node.
     * 
     * @param beginLine
     *            the begin line of this node
     */
    public final void setBeginLine(final int beginLine) {
        this.beginLine = beginLine;
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param comment to be set
     */
    public final void setComment(final Comment comment) {
        if (comment != null && (this instanceof Comment)) {
            throw new RuntimeException("A comment can not be commented");
        }
        if (this.comment != null)
        {
            this.comment.setCommentedNode(null);
        }
        this.comment = comment;
        if (comment != null) {
            this.comment.setCommentedNode(this);
        }
    }

    /**
     * Use this to store additional information to this node.
     *
     * @param data to be set
     */
    public final void setData(final Object data) {
        this.data = data;
    }

    /**
     * Sets the end column of this node.
     * 
     * @param endColumn
     *            the end column of this node
     */
    public final void setEndColumn(final int endColumn) {
        this.endColumn = endColumn;
    }

    /**
     * Sets the end line of this node.
     * 
     * @param endLine
     *            the end line of this node
     */
    public final void setEndLine(final int endLine) {
        this.endLine = endLine;
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

    public List<Node> getChildrenNodes() {
        return childrenNodes;
    }

    public boolean contains(Node other) {
        if (getBeginLine() > other.getBeginLine()) return false;
        if (getBeginLine() == other.getBeginLine() && getBeginColumn() > other.getBeginColumn()) return false;
        if (getEndLine() < other.getEndLine()) return false;
        if (getEndLine() == other.getEndLine() && getEndColumn() < other.getEndColumn()) return false;
        return true;
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
     * When more than one comments preceed a statement, the one immediately preceeding it
     * it is associated with the statements, while the others are "orphan".
     * @return all comments that cannot be attributed to a concept
     */
    public List<Comment> getOrphanComments() {
        return orphanComments;
    }

    /**
     * This is the list of Comment which are contained in the Node either because
     * they are properly associated to one of its children or because they are floating
     * around inside the Node
     * @return all Comments within the node as a list
     */
    public List<Comment> getAllContainedComments() {
        List<Comment> comments = new LinkedList<Comment>();
        comments.addAll(getOrphanComments());

        for (Node child : getChildrenNodes()) {
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
            Iterator<? extends Node> it = childNodes.iterator();
            while (it.hasNext()) {
                Node current = it.next();
                current.setParentNode(this);
            }
        }
    }

    protected void setAsParentNodeOf(Node childNode) {
        if (childNode != null) {
            childNode.setParentNode(this);
        }
    }

    public static final int ABSOLUTE_BEGIN_LINE = -1;
    public static final int ABSOLUTE_END_LINE = -2;

    public boolean isPositionedAfter(int line, int column) {
        if (line == ABSOLUTE_BEGIN_LINE) return true;
        if (getBeginLine() > line) {
            return true;
        } else if (getBeginLine() == line) {
            return getBeginColumn() > column;
        } else {
            return false;
        }
    }

    public boolean isPositionedBefore(int line, int column) {
        if (line == ABSOLUTE_END_LINE) return true;
        if (getEndLine() < line) {
            return true;
        } else if (getEndLine() == line) {
            return getEndColumn() < column;
        } else {
            return false;
        }
    }

    public boolean hasComment()
    {
        return comment != null;
    }
}
