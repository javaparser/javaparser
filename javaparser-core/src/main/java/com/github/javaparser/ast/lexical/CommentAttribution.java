package com.github.javaparser.ast.lexical;

import com.github.javaparser.ast.Node;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * @author Didier Villevalois
 */
public class CommentAttribution {

    /**
     * Attributes the comments to the AST node. The comments must be available in the run of the node.
     *
     * @param node          the node on which to attribute comments
     * @param removeLexemes whether to remove lexemes after comment attribution
     */
    public static void attributeComments(Node node, boolean removeLexemes) {
        Lexeme first = node.first();
        Lexeme last = node.last();
        if (first == null || last == null) return;

        // Rewind up to first lexeme
        Lexeme current = first;
        Lexeme previous = current.previous();
        while (previous != null) {
            current = previous;
            previous = current.previous();
        }

        doAttributeComments(null, node, current, removeLexemes);
    }

    private static Lexeme doAttributeComments(Node parent, Node node, Lexeme current, boolean removeLexemes) {
        List<Comment> comments = null;
        Comment javadocComment = null;

        boolean inEmptyLine = false;
        boolean hadEmptyLine = false;

        Lexeme first = node.first();
        Lexeme last = node.last();

        // Traverse up to the first meaningful lexeme
        while (current != first) {

            // Detect empty lines
            boolean isWhitespace = current.is(LexemeKind.WHITESPACE);
            if (isWhitespace) {
                boolean isNewLine = current.is(WhitespaceKind.LINE_ENDING);
                if (isNewLine) {
                    hadEmptyLine = inEmptyLine;
                    inEmptyLine = true;
                }
            } else {
                inEmptyLine = false;
            }

            // Collect comments
            boolean isComment = current.is(LexemeKind.COMMENT);
            if (isComment) {
                Comment comment = (Comment) current;

                comments = safeAdd(comments, comment);
                if (comment.is(CommentKind.JAVA_DOC)) {
                    javadocComment = comment;
                }
            }

            // If we collected comments before an empty line or a meaningful lexeme,
            // Then attribute those to the parent
            if (hadEmptyLine || !(isWhitespace || isComment)) {
                if (comments != null && !comments.isEmpty()) {
                    attributes(parent).addDanglingComments(comments);
                    comments.clear();
                    hadEmptyLine = false;
                }
            }

            current = advance(current, removeLexemes);
        }

        // If we collected comments, attribute those to the node
        if (comments != null && !comments.isEmpty()) {
            attributes(node).addLeadingComments(comments);
            comments.clear();
        }
        if (javadocComment != null) {
            attributes(node).setJavadocComment(javadocComment);
        }

        // Traverse the children nodes
        if (!isLeaf(node)) {
            // We sort the children nodes because they are not always in lexical order
            // TODO Investigate if we can use another mechanism like a visitor
            List<Node> children = new ArrayList<Node>(node.getChildrenNodes());
            Collections.sort(children, Node.BEGIN_POSITION_COMPARATOR);

            for (Node child : children) {
                current = doAttributeComments(node, child, current, removeLexemes);
            }
        }

        // Traverse up to the last meaningful lexeme
        while (current != last) {
            // If there are remaining comments, attribute those to the node
            boolean isComment = current.is(LexemeKind.COMMENT);
            if (isComment) {
                Comment comment = (Comment) current;
                attributes(node).addDanglingComment(comment);
            }

            current = advance(current, removeLexemes);
        }

        // Traverse up to the trailing comment lexeme, if any
        Lexeme parentLast = parent == null ? null : parent.last();
        while (current != parentLast && current.next() != null) {
            current = advance(current, removeLexemes);

            boolean isWhitespace = current.is(LexemeKind.WHITESPACE);
            boolean isNewLineOrEndOfFile = isWhitespace &&
                    current.is(WhitespaceKind.LINE_ENDING, WhitespaceKind.END_OF_FILE);
            boolean isSingleLineComment = current.is(LexemeKind.COMMENT) && current.is(CommentKind.SINGLE_LINE);

            // If we hit end of line or a meaningful lexeme, then dismiss
            if (!(isWhitespace || isSingleLineComment) || isNewLineOrEndOfFile) break;

            // If there is a trailing comment, attribute it to the node
            if (isSingleLineComment) {
                attributes(node).setTrailingComment((Comment) current);
            }
        }

        if (removeLexemes) {
            // Clear references to the run
            node.setFirst(null);
            node.setLast(null);
        }

        return current;
    }

    private static Lexeme advance(Lexeme current, boolean removeLexemes) {
        Lexeme next = current.next();
        if (removeLexemes) {
            // Cut the run's doubly-linked list
            current.setPrevious(null);
            current.setNext(null);
        }
        return next;
    }

    private static List<Comment> safeAdd(List<Comment> comments, Comment current) {
        if (comments == null) comments = new ArrayList<Comment>();
        comments.add(current);
        return comments;
    }

    private static boolean isLeaf(Node node) {
        List<Node> children = node.getChildrenNodes();
        return children == null || children.isEmpty();
    }

    private static CommentAttributes attributes(Node node) {
        CommentAttributes attributes = node.getCommentAttributes();
        if (attributes == null) {
            attributes = new CommentAttributes();
            node.setCommentAttributes(attributes);
        }
        return attributes;
    }
}
