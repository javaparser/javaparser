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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.LineComment;
import com.github.javaparser.utils.PositionUtils;

import java.util.*;

import static com.github.javaparser.ast.Node.NODE_BY_BEGIN_POSITION;

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
        if (comments.isEmpty())
            return;

        /* I should sort all the direct children and the comments, if a comment
         is the first thing then it
         a comment to the CompilationUnit */

        // FIXME if there is no package it could be also a comment to the following class...
        // so I could use some heuristics in these cases to distinguish the two
        // cases

        List<Node> children = cu.getChildrenNodes();
        PositionUtils.sortByBeginPosition(children);

        Comment firstComment = comments.iterator().next();
        if (cu.getPackage() != null
                && (children.isEmpty() || PositionUtils.areInOrder(
                firstComment, children.get(0)))) {
            cu.setComment(firstComment);
            comments.remove(firstComment);
        }
    }

    /**
     * This method try to attributes the nodes received to child of the node. It
     * returns the node that were not attributed.
     */
    void insertComments(Node node, TreeSet<Comment> commentsToAttribute) {
        if (commentsToAttribute.isEmpty())
            return;
        
        if(node instanceof CompilationUnit){
            insertComments((CompilationUnit)node, commentsToAttribute);
        }

        // the comments can:
        // 1) Inside one of the child, then it is the child that have to
        // associate them
        // 2) If they are not inside a child they could be preceeding nothing, a
        // comment or a child
        // if they preceed a child they are assigned to it, otherweise they
        // remain "orphans"

        List<Node> children = node.getChildrenNodes();
        PositionUtils.sortByBeginPosition(children);

        for (Node child : children) {
            TreeSet<Comment> commentsInsideChild = new TreeSet<>(NODE_BY_BEGIN_POSITION);
            for (Comment c : commentsToAttribute) {
                if (PositionUtils.nodeContains(child, c,
                        configuration.doNotConsiderAnnotationsAsNodeStartForCodeAttribution)) {
                    commentsInsideChild.add(c);
                }
            }
            commentsToAttribute.removeAll(commentsInsideChild);
            insertComments(child, commentsInsideChild);
        }

        /* I can attribute in line comments to elements preceeding them, if
         there is something contained in their line */
        List<Comment> attributedComments = new LinkedList<>();
        for (Comment comment : commentsToAttribute) {
            if (comment.isLineComment()) {
                for (Node child : children) {
                    if (child.getEnd().line == comment.getBegin().line
                        && attributeLineCommentToNodeOrChild(child,
                                comment.asLineComment())) {
                            attributedComments.add(comment);
                    }
                }
            }
        }

        /* at this point I create an ordered list of all remaining comments and
         children */
        Comment previousComment = null;
        attributedComments = new LinkedList<>();
        List<Node> childrenAndComments = new LinkedList<>();
        childrenAndComments.addAll(children);
        childrenAndComments.addAll(commentsToAttribute);
        PositionUtils.sortByBeginPosition(childrenAndComments,
                configuration.doNotConsiderAnnotationsAsNodeStartForCodeAttribution);

        for (Node thing : childrenAndComments) {
            if (thing instanceof Comment) {
                previousComment = (Comment) thing;
                if (!previousComment.isOrphan()) {
                    previousComment = null;
                }
            } else {
                if (previousComment != null && !thing.hasComment()) {
                    if (!configuration.doNotAssignCommentsPrecedingEmptyLines
                            || !thereAreLinesBetween(previousComment, thing)) {
                        thing.setComment(previousComment);
                        attributedComments.add(previousComment);
                        previousComment = null;
                    }
                }
            }
        }

        commentsToAttribute.removeAll(attributedComments);

        // all the remaining are orphan nodes
        for (Comment c : commentsToAttribute) {
            if (c.isOrphan()) {
                node.addOrphanComment(c);
            }
        }
    }

    private boolean attributeLineCommentToNodeOrChild(Node node, LineComment lineComment) {
        // The node start and end at the same line as the comment,
        // let's give to it the comment
        if (node.getBegin().line == lineComment.getBegin().line
                && !node.hasComment()) {
            if(!(node instanceof Comment)) {
                node.setComment(lineComment);
            }
            return true;
        } else {
            // try with all the children, sorted by reverse position (so the
            // first one is the nearest to the comment
            List<Node> children = new LinkedList<Node>();
            children.addAll(node.getChildrenNodes());
            PositionUtils.sortByBeginPosition(children);
            Collections.reverse(children);

            for (Node child : children) {
                if (attributeLineCommentToNodeOrChild(child, lineComment)) {
                    return true;
                }
            }

            return false;
        }
    }

    private boolean thereAreLinesBetween(Node a, Node b) {
        if (!PositionUtils.areInOrder(a, b)) {
            return thereAreLinesBetween(b, a);
        }
        int endOfA = a.getEnd().line;
        return b.getBegin().line > (endOfA + 1);
    }

}
