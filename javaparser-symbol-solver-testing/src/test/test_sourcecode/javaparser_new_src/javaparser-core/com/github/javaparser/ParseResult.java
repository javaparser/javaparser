package com.github.javaparser;

import com.github.javaparser.ast.comments.CommentsCollection;

import java.util.List;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.Collections.singletonList;

import static com.github.javaparser.utils.Utils.EOL;

/**
 * The results given when parsing with an instance of JavaParser.
 */
public class ParseResult<T> {
    private final Optional<T> result;
    private final List<Problem> problems;
    private final Optional<List<Token>> tokens;
    private final Optional<CommentsCollection> commentsCollection;

    /**
     * General constructor.
     * @param result the AST, or empty if it wasn't created.
     * @param problems a list of encountered parsing problems.
     * @param tokens the complete list of tokens that were parsed, or empty if parsing failed completely.
     */
    ParseResult(Optional<T> result, List<Problem> problems, Optional<List<Token>> tokens, Optional<CommentsCollection> commentsCollection) {
        this.commentsCollection = assertNotNull(commentsCollection);
        this.result = assertNotNull(result);
        this.problems = assertNotNull(problems);
        this.tokens = assertNotNull(tokens);
    }

    /**
     * Used when parsing failed completely with an exception.
     */
    ParseResult(Throwable throwable) {
        this(Optional.empty(), singletonList(new Problem(throwable.getMessage(), Optional.empty(), Optional.of(throwable))), Optional.empty(), Optional.empty());
    }

    /**
     * @return if parsing was successful, meaning no errors of any kind were encountered.
     */
    public boolean isSuccessful() {
        return problems.isEmpty() && result.isPresent();
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
        return tokens;
    }

    /**
     * @return the complete collection of comments encountered while parsing.
     */
    public Optional<CommentsCollection> getCommentsCollection() {
        return commentsCollection;
    }

    /**
     * @return the AST of the parsed source code, or empty if parsing failed completely.
     */
    public Optional<T> getResult() {
        return result;
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
