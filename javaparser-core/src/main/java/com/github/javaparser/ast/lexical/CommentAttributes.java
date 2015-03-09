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

package com.github.javaparser.ast.lexical;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Didier Villevalois
 */
public class CommentAttributes {

    private List<Comment> leadingComments;
    private Comment javadocComment;
    private List<Comment> danglingComments;
    private Comment trailingComment;

    public void setLeadingComments(List<Comment> leadingComments) {
        this.leadingComments = leadingComments;
    }

    public void addLeadingComment(Comment comment) {
        if (leadingComments == null) {
            leadingComments = new ArrayList<Comment>();
        }
        leadingComments.add(comment);
    }

    public void addLeadingComments(List<Comment> comments) {
        if (leadingComments == null) {
            leadingComments = new ArrayList<Comment>();
        }
        leadingComments.addAll(comments);
    }

    public void setJavadocComment(Comment comment) {
        javadocComment = comment;
    }

    public void setDanglingComments(List<Comment> danglingComments) {
        this.danglingComments = danglingComments;
    }

    public void addDanglingComment(Comment comment) {
        if (danglingComments == null) {
            danglingComments = new ArrayList<Comment>();
        }
        danglingComments.add(comment);
    }

    public void addDanglingComments(List<Comment> comments) {
        if (danglingComments == null) {
            danglingComments = new ArrayList<Comment>();
        }
        danglingComments.addAll(comments);
    }

    public void setTrailingComment(Comment comment) {
        trailingComment = comment;
    }

    public List<Comment> getLeadingComments() {
        return leadingComments;
    }

    public Comment getJavadocComment() {
        return javadocComment;
    }

    public List<Comment> getDanglingComments() {
        return danglingComments;
    }

    public Comment getTrailingComment() {
        return trailingComment;
    }

    public boolean isEmpty() {
        return (leadingComments == null || leadingComments.isEmpty()) &&
                (danglingComments == null || danglingComments.isEmpty()) &&
                javadocComment == null && trailingComment == null;
    }
}
