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

import java.util.Collection;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static com.github.javaparser.ast.Node.NODE_BY_BEGIN_POSITION;

/**
 * The comments contained in a certain parsed piece of source code.
 */
public class CommentsCollection {
    private final TreeSet<Comment> comments = new TreeSet<>(NODE_BY_BEGIN_POSITION);

    public CommentsCollection() {
    }

    public CommentsCollection(Collection<Comment> commentsToCopy) {
        comments.addAll(commentsToCopy);
    }

    public Set<LineComment> getLineComments() {
        return comments.stream()
                .filter(comment -> comment instanceof LineComment)
                .map(comment -> (LineComment) comment)
                .collect(Collectors.toCollection(() -> new TreeSet<>(NODE_BY_BEGIN_POSITION)));
    }

    public Set<BlockComment> getBlockComments() {
        return comments.stream()
                .filter(comment -> comment instanceof BlockComment)
                .map(comment -> (BlockComment) comment)
                .collect(Collectors.toCollection(() -> new TreeSet<>(NODE_BY_BEGIN_POSITION)));
    }

    public Set<JavadocComment> getJavadocComments() {
        return comments.stream()
                .filter(comment -> comment instanceof JavadocComment)
                .map(comment -> (JavadocComment) comment)
                .collect(Collectors.toCollection(() -> new TreeSet<>(NODE_BY_BEGIN_POSITION)));
    }

    public void addComment(Comment comment) {
        comments.add(comment);
    }

    public boolean contains(Comment comment) {
        if (!comment.getRange().isPresent()) {
            return false;
        }
        Range commentRange = comment.getRange().get();
        for (Comment c : getComments()) {
            if (!c.getRange().isPresent()) {
                return false;
            }
            Range cRange = c.getRange().get();
            // we tolerate a difference of one element in the end column:
            // it depends how \r and \n are calculated...
            if (cRange.begin.equals(commentRange.begin) &&
                    cRange.end.line == commentRange.end.line &&
                    Math.abs(cRange.end.column - commentRange.end.column) < 2) {
                return true;
            }
        }
        return false;
    }

    public TreeSet<Comment> getComments() {
        return comments;
    }

    public int size() {
        return comments.size();
    }

    public CommentsCollection minus(CommentsCollection other) {
        CommentsCollection result = new CommentsCollection();
        result.comments.addAll(
                comments.stream()
                        .filter(comment -> !other.contains(comment))
                        .collect(Collectors.toList()));
        return result;
    }

    public CommentsCollection copy() {
        return new CommentsCollection(comments);
    }
}
