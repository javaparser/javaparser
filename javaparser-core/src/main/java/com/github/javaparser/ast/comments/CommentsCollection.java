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

import java.util.LinkedList;
import java.util.List;

/**
 * Set of comments produced by CommentsParser.
 */
public class CommentsCollection {
    private List<LineComment> lineCommentsList = new LinkedList<LineComment>();
    private List<BlockComment> blockCommentsList = new LinkedList<BlockComment>();
    private List<JavadocComment> javadocCommentsList = new LinkedList<JavadocComment>();

    public List<LineComment> getLineCommentsList(){
        return lineCommentsList;
    }

    public List<BlockComment> getBlockCommentsList(){
        return blockCommentsList;
    }

    public List<JavadocComment> getJavadocCommentsList(){
        return javadocCommentsList;
    }

    public void addComment(LineComment lineComment){
        this.lineCommentsList.add(lineComment);
    }

    public void addComment(BlockComment blockComment){
        this.blockCommentsList.add(blockComment);
    }

    public void addComment(JavadocComment javadocComment){
        this.javadocCommentsList.add(javadocComment);
    }

    public boolean contains(Comment comment){
        for (Comment c : getAll()){
            // we tolerate a difference of one element in the end column:
            // it depends how \r and \n are calculated...
            if ( c.getBegin().line==comment.getBegin().line &&
                 c.getBegin().column==comment.getBegin().column &&
                 c.getEnd().line==comment.getEnd().line &&
                 Math.abs(c.getEnd().column-comment.getEnd().column)<2 ){
                return true;
            }
        }
        return false;
    }

    public List<Comment> getAll(){
        List<Comment> commentsList = new LinkedList<Comment>();
        commentsList.addAll(lineCommentsList);
        commentsList.addAll(blockCommentsList);
        commentsList.addAll(javadocCommentsList);
        return commentsList;
    }

    public int size(){
        return lineCommentsList.size()+ blockCommentsList.size()+ javadocCommentsList.size();
    }

    public CommentsCollection minus(CommentsCollection other){
        CommentsCollection result = new CommentsCollection();
        for (LineComment comment : lineCommentsList){
            if (!other.contains(comment)){
                result.lineCommentsList.add(comment);
            }
        }
        for (BlockComment comment : blockCommentsList){
            if (!other.contains(comment)){
                result.blockCommentsList.add(comment);
            }
        }
        for (JavadocComment comment : javadocCommentsList){
            if (!other.contains(comment)){
                result.javadocCommentsList.add(comment);
            }
        }
        return result;
    }
}
