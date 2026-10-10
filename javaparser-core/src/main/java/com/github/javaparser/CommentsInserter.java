/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
package com.github.javaparser;

import static com.github.javaparser.ast.Node.NODE_BY_BEGIN_POSITION;
import static java.util.stream.Collectors.toList;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.utils.PositionUtils;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.TreeSet;

/**
 * Assigns comments to nodes of the AST.
 *
 * @author Sebastian Kuerten
 * @author Júlio Vilmar Gesser
 */
class CommentsInserter {

    private final ParserConfiguration configuration;

    CommentsInserter(ParserConfiguration configuration) {
        this.configuration = configuration;
    }

    /**
     * Comments are attributed to the thing they comment and are removed from
     * the comments.
     */
    private void insertComments(CompilationUnit cu, TreeSet<Comment> comments) {
        if (comments.isEmpty()) return;
        /* I should sort all the direct children and the comments, if a comment
        is the first thing then it is a comment to the CompilationUnit */
        // FIXME if there is no package it could be also a comment to the following class...
        // so I could use some heuristics in these cases to distinguish the two
        // cases
        List<Node> children = cu.getChildNodes();
        Comment firstComment = comments.iterator().next();
        if (cu.getPackageDeclaration().isPresent()
                && (children.isEmpty()
                        || PositionUtils.areInOrder(
                                firstComment, cu.getPackageDeclaration().get()))) {
            cu.setComment(firstComment);
            comments.remove(firstComment);
        }
    }

    /**
     * This method try to attributes the nodes received to child of the node. It
     * returns the node that were not attributed.
     */
    void insertComments(Node node, TreeSet<Comment> commentsToAttribute) {
        if (commentsToAttribute.isEmpty()) return;
        if (node instanceof CompilationUnit) {
            insertComments((CompilationUnit) node, commentsToAttribute);
        }
        /* the comment can...
        1) be inside one of the children, then the comment should be associated to this child
        2) be outside all children. They could be preceding nothing, a comment or a child.
           If they preceed a child they are assigned to it, otherwise they remain "orphans"
        */
        // Never attribute comments to modifiers.
        List<Node> // Never attribute comments to modifiers.
                children = node.getChildNodes().stream()
                        .filter(n -> !(n instanceof Modifier))
                        .collect(toList());
        boolean attributeToAnnotation = !(configuration.isIgnoreAnnotationsWhenAttributingComments());
        for (Node child : children) {
            if (commentsToAttribute.isEmpty()) {
                break;
            }
            // Some child nodes of a compact class declaration may not have a range, so first check that the child
            // in question does have a range.
            if (!child.hasRange()) {
                continue;
            }
            // Move the comments inside the child from the pending ones to the child's own.
            TreeSet<Comment> commentsInsideChild = new TreeSet<>(NODE_BY_BEGIN_POSITION);
            Iterator<Comment> candidates = commentsBeginningIn(
                            commentsToAttribute, child.getRange().get())
                    .iterator();
            while (candidates.hasNext()) {
                Comment comment = candidates.next();
                if (PositionUtils.nodeContains(child, comment, !attributeToAnnotation)) {
                    commentsInsideChild.add(comment);
                    candidates.remove();
                }
            }
            insertComments(child, commentsInsideChild);
        }
        attributeLineCommentsOnSameLine(commentsToAttribute, children);
        /* if a comment is on the line right before a node it should belong
        to that node*/
        if (!commentsToAttribute.isEmpty()) {
            if (commentIsOnNextLine(node, commentsToAttribute.first())) {
                node.setComment(commentsToAttribute.first());
                commentsToAttribute.remove(commentsToAttribute.first());
            }
        }
        /* at this point I create an ordered list of all remaining comments and
        children */
        Comment previousComment = null;
        final List<Comment> attributedComments = new LinkedList<>();
        List<Node> childrenAndComments = new LinkedList<>();
        // Avoid attributing comments to a meaningless container.
        childrenAndComments.addAll(children);
        commentsToAttribute.removeAll(attributedComments);
        childrenAndComments.addAll(commentsToAttribute);
        PositionUtils.sortByBeginPosition(
                childrenAndComments, configuration.isIgnoreAnnotationsWhenAttributingComments());
        for (Node thing : childrenAndComments) {
            if (thing instanceof Comment) {
                previousComment = (Comment) thing;
                if (!previousComment.isOrphan()) {
                    previousComment = null;
                }
            } else {
                if (previousComment != null && !thing.getComment().isPresent()) {
                    if (!configuration.isDoNotAssignCommentsPrecedingEmptyLines()
                            || !thereAreLinesBetween(previousComment, thing)) {
                        thing.setComment(previousComment);
                        attributedComments.add(previousComment);
                        previousComment = null;
                    }
                }
            }
        }
        removeAttributed(commentsToAttribute, attributedComments);
        // all the remaining are orphan nodes
        for (Comment c : commentsToAttribute) {
            if (c.isOrphan()) {
                node.addOrphanComment(c);
            }
        }
    }

    /**
     * Removes the attributed comments one by one, each found through the set's order. ({@code removeAll} would instead
     * search the list for every comment in the set whenever the set is no larger than the list.)
     */
    private static void removeAttributed(TreeSet<Comment> comments, List<Comment> attributed) {
        attributed.forEach(comments::remove);
    }

    /**
     * The comments that begin inside the range: only these can lie inside a node with that range. Looking them up
     * through the comments' order by begin position, rather than testing every comment, keeps attribution from
     * growing with the number of children times the number of comments. Comments without a range are never inside.
     */
    private static NavigableSet<Comment> commentsBeginningIn(TreeSet<Comment> comments, Range range) {
        return comments.subSet(commentBeginningAt(range.begin), true, commentBeginningAt(range.end), true);
    }

    /**
     * A stand-in for looking comments up by where they begin, which is all their order compares.
     */
    private static Comment commentBeginningAt(Position position) {
        Comment comment = new BlockComment();
        comment.setRange(Range.range(position, position));
        return comment;
    }

    private void attributeLineCommentsOnSameLine(TreeSet<Comment> commentsToAttribute, List<Node> children) {
        /* I can attribute in line comments to elements preceeding them, if
        there is something contained in their line */
        if (commentsToAttribute.stream().noneMatch(Comment::isLineComment)) {
            return;
        }
        List<Comment> attributedComments = new LinkedList<>();
        // The children ending on each line, in order: a line comment can only trail those ending on its own line.
        Map<Integer, List<Node>> childrenEndingOnLine = new HashMap<>();
        for (Node child : children) {
            if (child.hasRange()) {
                childrenEndingOnLine
                        .computeIfAbsent(child.getRange().get().end.line, line -> new ArrayList<>())
                        .add(child);
            }
        }
        commentsToAttribute.stream()
                .filter(comment -> comment.hasRange())
                .filter(Comment::isLineComment)
                .forEach(comment -> {
                    Position commentBegin = comment.getRange().get().begin;
                    // Candidates: children whose end is on the comment's line and
                    // before it, i.e. the nodes the comment could trail. Sort them by
                    // begin position and try from the nearest (greatest begin) backwards,
                    // stopping at the first one that accepts the comment. The previous
                    // implementation iterated every such sibling without stopping, so the
                    // same comment object was set on several of them. Trying in order and
                    // breaking on first accept keeps the attribution unique while still
                    // falling back to an earlier sibling when the nearest one refuses
                    // (e.g. it already carries a comment), matching the old behavior.
                    List<Node> trailing = new LinkedList<>();
                    for (Node child : childrenEndingOnLine.getOrDefault(commentBegin.line, Collections.emptyList())) {
                        Position childEnd = child.getRange().get().end;
                        // Excludes a child that starts to the right of the comment on
                        // the same line: it cannot be what the comment trails.
                        if (childEnd.isBefore(commentBegin)) {
                            trailing.add(child);
                        }
                    }
                    PositionUtils.sortByBeginPosition(
                            trailing, configuration.isIgnoreAnnotationsWhenAttributingComments());
                    Collections.reverse(trailing);
                    for (Node candidate : trailing) {
                        if (attributeLineCommentToNodeOrChild(candidate, comment.asLineComment())) {
                            attributedComments.add(comment);
                            break;
                        }
                    }
                });
        removeAttributed(commentsToAttribute, attributedComments);
    }

    private boolean attributeLineCommentToNodeOrChild(Node node, LineComment lineComment) {
        if (!node.hasRange() || !lineComment.hasRange()) {
            return false;
        }
        // The node start and end at the same line as the comment,
        // let's give to it the comment
        if (node.getBegin().get().line == lineComment.getBegin().get().line
                && !node.getComment().isPresent()) {
            if (!(node instanceof Comment)) {
                node.setComment(lineComment);
            }
            return true;
        }
        // try with the children spanning the comment's line, sorted by reverse
        // position so the first one is the nearest to the comment. Only such a
        // child can be, or contain, a node beginning on that line.
        int commentLine = lineComment.getBegin().get().line;
        List<Node> children = new ArrayList<>();
        for (Node child : node.getChildNodes()) {
            if (child.hasRange()
                    && child.getBegin().get().line <= commentLine
                    && commentLine <= child.getEnd().get().line) {
                children.add(child);
            }
        }
        PositionUtils.sortByBeginPosition(children);
        Collections.reverse(children);
        for (Node child : children) {
            if (attributeLineCommentToNodeOrChild(child, lineComment)) {
                return true;
            }
        }
        return false;
    }

    private boolean thereAreLinesBetween(Node a, Node b) {
        if (!a.hasRange() || !b.hasRange()) {
            return true;
        }
        if (!PositionUtils.areInOrder(a, b)) {
            return thereAreLinesBetween(b, a);
        }
        int endOfA = a.getEnd().get().line;
        return b.getBegin().get().line > endOfA + 1;
    }

    private boolean commentIsOnNextLine(Node a, Comment c) {
        if (!c.hasRange() || !a.hasRange()) return false;
        return c.getRange().get().end.line + 1 == a.getRange().get().begin.line;
    }
}
