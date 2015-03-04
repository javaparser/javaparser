/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.ast.comments;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.lexical.Lexeme;

/**
 * Abstract class for all AST nodes that represent comments.
 * 
 * @see BlockComment
 * @see LineComment
 * @see JavadocComment
 * @author Julio Vilmar Gesser
 */
public abstract class Comment extends Node {

    private String content;
    private Node commentedNode;

    public Comment() {
    }

    public Comment(String content) {
        this.content = content;
    }

    public Comment(Lexeme first, Lexeme last, String content) {
        super(first, last);
        this.content = content;
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
     * @param content
     *            the text of the comment to set
     */
    public void setContent(String content) {
        this.content = content;
    }

    public boolean isLineComment()
    {
        return false;
    }

    public LineComment asLineComment()
    {
        if (isLineComment())
        {
            return (LineComment) this;
        } else {
            throw new UnsupportedOperationException("Not a line comment");
        }
    }

    public Node getCommentedNode()
    {
        return this.commentedNode;
    }

    public void setCommentedNode(Node commentedNode)
    {
        if (commentedNode==null)
        {
            this.commentedNode = commentedNode;
            return;
        }
        if (commentedNode==this)
        {
            throw new IllegalArgumentException();
        }
        if (commentedNode instanceof Comment)
        {
            throw new IllegalArgumentException();
        }
        this.commentedNode = commentedNode;
    }

    public boolean isOrphan()
    {
        return this.commentedNode == null;
    }
}
