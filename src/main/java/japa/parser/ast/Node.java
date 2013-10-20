/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
 *
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 05/10/2006
 */
package japa.parser.ast;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import japa.parser.ast.visitor.DumpVisitor;
import japa.parser.ast.visitor.EqualsVisitor;
import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

/**
 * Abstract class for all nodes of the AST.
 * 
 * @author Julio Vilmar Gesser
 */
public abstract class Node {

	private int beginLine;

	private int beginColumn;

	private int endLine;

	private int endColumn;
	
	private Node parentNode;

    private List<Node> childrenNodes =  new LinkedList<Node>();
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
	 * Use this to retrieve comment associated to this node.
	 */
	public final Comment getComment() {
		return comment;
	}

	/**
	 * Use this to retrieve additional information associated to this node.
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
	 */
	public final void setComment(final Comment comment) {
		this.comment = comment;
	}

	/**
	 * Use this to store additional information to this node.
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
	@Override public final String toString() {
		final DumpVisitor visitor = new DumpVisitor();
		accept(visitor, null);
		return visitor.getSource();
	}

	@Override public final int hashCode() {
		return toString().hashCode();
	}

	@Override public boolean equals(final Object obj) {
		return EqualsVisitor.equals(this, (Node) obj);
	}

	public Node getParentNode() {
		return parentNode;
	}

    public List<Node> getChildrenNodes(){
        return childrenNodes;
    }

    public boolean contains(Node other){
        if (getBeginLine()>other.getBeginLine()) return false;
        if (getBeginLine()==other.getBeginLine() && getBeginColumn()>other.getBeginColumn()) return false;
        if (getEndLine()<other.getEndLine()) return false;
        if (getEndLine()==other.getEndLine() && getEndColumn()<other.getEndColumn()) return false;
        return true;
    }

    public void addOrphanComment(Comment comment){
        orphanComments.add(comment);
        comment.setParentNode(this);
    }

    public List<Comment> getOrphanComments(){
        return orphanComments;
    }

	public void setParentNode(Node parentNode) {
		this.parentNode = parentNode;
        this.parentNode.childrenNodes.add(this);
	}

	protected void setAsParentNodeOf(List<? extends Node> childNodes) {
		if(childNodes != null){
			Iterator<? extends Node> it = childNodes.iterator();
			while(it.hasNext()){
				Node current = it.next();
				current.setParentNode(this);
			}
		}
	}

	protected void setAsParentNodeOf(Node childNode) {
		if(childNode != null){
			childNode.setParentNode(this);
		}
	}
}
