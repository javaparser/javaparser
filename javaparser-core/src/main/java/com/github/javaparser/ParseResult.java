package com.github.javaparser;

import java.util.List;
import java.util.Optional;

import static java.util.Collections.singletonList;

import static com.github.javaparser.utils.Utils.EOL;

/**
 * The results given when parsing with an instance of JavaParser.
 */
public class ParseResult<T> {
    private final Optional<T> result;
    private final List<Problem> problems;
    private final Optional<List<Token>> tokens;

    /**
     * General constructor.
     * @param result the AST, or empty if it wasn't created.
     * @param problems a list of encountered parsing problems.
     * @param tokens the complete list of tokens that were parsed.
     */
    ParseResult(Optional<T> result, List<Problem> problems, Optional<List<Token>> tokens) {
        this.result = result;
        this.problems = problems;
        this.tokens = tokens;
    }

    /**
     * Used when parsing failed completely with an exception.
     */
    ParseResult(Throwable throwable) {
        this(Optional.empty(), singletonList(new Problem(throwable.getMessage(), Optional.empty(), Optional.of(throwable))), Optional.empty());
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
     * @return the complete list of tokens that were parsed.
     */
    public Optional<List<Token>> getTokens() {
        return tokens;
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
