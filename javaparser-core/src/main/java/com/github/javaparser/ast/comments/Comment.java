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
package com.github.javaparser.ast.comments;

import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.observer.ObservableProperty;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.CommentMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;

/**
 * Abstract class for all AST nodes that represent comments.
 *
 * @author Julio Vilmar Gesser
 * @see BlockComment
 * @see LineComment
 * @see JavadocComment
 */
public abstract class Comment extends Node {

    private String content;

    private Node commentedNode;

    public Comment(Range range, String content) {
        super(range);
        setContent(content);
    }

    /**
     * Return the text of the comment.
     *
     * @return text of the comment
     */
    public final String getContent() {
        return content;
    }

    /**
     * Sets the text of the comment.
     *
     * @param content the text of the comment to set
     */
    public Comment setContent(final String content) {
        assertNotNull(content);
        notifyPropertyChange(ObservableProperty.CONTENT, this.content, content);
        this.content = content;
        return this;
    }

    public boolean isLineComment() {
        return false;
    }

    public LineComment asLineComment() {
        if (isLineComment()) {
            return (LineComment) this;
        } else {
            throw new UnsupportedOperationException("Not a line comment");
        }
    }

    public Optional<Node> getCommentedNode() {
        return Optional.ofNullable(this.commentedNode);
    }

    /**
     * Sets the commentedNode
     *
     * @param commentedNode the commentedNode, can be null
     * @return this, the Comment
     */
    public Comment setCommentedNode(Node commentedNode) {
        notifyPropertyChange(ObservableProperty.COMMENTED_NODE, this.commentedNode, commentedNode);
        if (commentedNode == null) {
            this.commentedNode = null;
            return this;
        }
        if (commentedNode == this) {
            throw new IllegalArgumentException();
        }
        if (commentedNode instanceof Comment) {
            throw new IllegalArgumentException();
        }
        this.commentedNode = commentedNode;
        return this;
    }

    public boolean isOrphan() {
        return this.commentedNode == null;
    }

    @Override
    public boolean remove() {
        // the other are orphan comments and remove should work with them
        if (this.commentedNode != null) {
            this.commentedNode.setComment(null);
            return true;
        } else if (this.getParentNode().isPresent()) {
            return this.getParentNode().get().removeOrphanComment(this);
        } else {
            return false;
        }
    }

    @Override
    public boolean remove(Node node) {
        if (node == null)
            return false;
        return super.remove(node);
    }

    @Override
    public Comment clone() {
        return (Comment) accept(new CloneVisitor(), null);
    }

    @Override
    public CommentMetaModel getMetaModel() {
        return JavaParserMetaModel.commentMetaModel;
    }
}
