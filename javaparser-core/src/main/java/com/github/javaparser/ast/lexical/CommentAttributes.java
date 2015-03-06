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
