package com.github.javaparser;

import static com.github.javaparser.utils.Utils.EOL;
import static java.util.Collections.singletonList;

import java.util.List;
import java.util.Optional;

import com.github.javaparser.ast.comments.CommentsCollection;

/**
 * The results given when parsing with an instance of JavaParser.
 */
public class ParseResult<T> {
    private final T result;
    private final List<Problem> problems;
    private final List<Token> tokens;
    private final CommentsCollection commentsCollection;

    /**
     * General constructor.
     * @param result the AST, or empty if it wasn't created.
     * @param problems a list of encountered parsing problems.
     * @param tokens the complete list of tokens that were parsed, or empty if parsing failed completely.
     */
    ParseResult(T result, List<Problem> problems, List<Token> tokens, CommentsCollection commentsCollection) {
        this.commentsCollection = commentsCollection;
        this.result = result;
        this.problems = problems;
        this.tokens = tokens;
    }

    /**
     * Used when parsing failed completely with an exception.
     */
    ParseResult(Throwable throwable) {
        this(null, singletonList(
                new Problem(createMessage(throwable), null, throwable)), null, null);
    }

    private static String createMessage(Throwable throwable) {
        String message = throwable.getMessage();
        if (message == null) {
            return throwable.getClass().getSimpleName();
        }
        return message;
    }

    /**
     * @return if parsing was successful, meaning no errors of any kind were encountered.
     */
    public boolean isSuccessful() {
        return problems.isEmpty() && result != null;
    }

    /**
     * @return the list of encountered parsing problems. Empty when no problems were encountered.
     */
    public List<Problem> getProblems() {
        return problems;
    }

    /**
     * @return the complete list of tokens that were parsed, or empty if parsing failed completely.
     */
    public Optional<List<Token>> getTokens() {
        return Optional.ofNullable(tokens);
    }

    /**
     * @return the complete collection of comments encountered while parsing.
     */
    public Optional<CommentsCollection> getCommentsCollection() {
        return Optional.ofNullable(commentsCollection);
    }

    /**
     * @return the AST of the parsed source code, or empty if parsing failed completely.
     */
    public Optional<T> getResult() {
        return Optional.ofNullable(result);
    }

    @Override
    public String toString() {
        if (isSuccessful()) {
            return "Parsing successful";
        }
        StringBuilder message = new StringBuilder("Parsing failed:").append(EOL);
        for (Problem problem : problems) {
            message.append(problem.toString()).append(EOL);
        }
        return message.toString();
    }
}
