package com.github.javaparser;

import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.comments.LineComment;

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.Position.pos;

/**
 * Base class for {@link com.github.javaparser.GeneratedJavaParserTokenManager}
 */
abstract class GeneratedJavaParserTokenManagerBase {
    /**
     * Create a TokenRange that spans exactly one token
     */
    private static TokenRange tokenRange(Token token) {
        JavaToken javaToken = token.javaToken;
        return new TokenRange(javaToken, javaToken);
    }

    /**
     * Since comments are completely captured in a single token, including their delimiters, deconstruct them here so we
     * can turn them into nodes later on.
     */
    static Comment createCommentFromToken(Token token) {
        String commentText = token.image;
        if (token.kind == JAVADOC_COMMENT) {
            return new JavadocComment(tokenRange(token), commentText.substring(3, commentText.length() - 2));
        } else if (token.kind == MULTI_LINE_COMMENT) {
            return new BlockComment(tokenRange(token), commentText.substring(2, commentText.length() - 2));
        } else if (token.kind == SINGLE_LINE_COMMENT) {
            // line comments have their end of line character(s) included, and we don't want that.
            Range range = new Range(pos(token.beginLine, token.beginColumn), pos(token.endLine, token.endColumn));
            while (commentText.endsWith("\r") || commentText.endsWith("\n")) {
                commentText = commentText.substring(0, commentText.length() - 1);
            }
            range = range.withEnd(pos(range.begin.line, range.begin.column + commentText.length()));
            LineComment comment = new LineComment(tokenRange(token), commentText.substring(2));
            comment.setRange(range);
            return comment;
        }
        throw new AssertionError("Unexpectedly got passed a non-comment token.");
    }
}
