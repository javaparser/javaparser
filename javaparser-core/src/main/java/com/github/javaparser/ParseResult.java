package com.github.javaparser;

import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import static java.util.Collections.singletonList;

/**
 * The results given when parsing with an instance of JavaParser.
 */
public class ParseResult<T> {
    public final Optional<T> result;
    public final List<Problem> problems;
    public final Optional<List<Token>> tokens;

    public ParseResult(Optional<T> result, List<Problem> problems, Optional<List<Token>> tokens) {
        this.result = result;
        this.problems = problems;
        this.tokens = tokens;
    }

    public ParseResult(Throwable throwable) {
        this(Optional.empty(), singletonList(new Problem(throwable.getMessage(), Optional.empty(), Optional.of(throwable))), Optional.empty());
    }

    public boolean isSuccessful() {
        return problems.isEmpty();
    }

    @Override
    public String toString() {
        if (isSuccessful()) {
            return "Parsing successful";
        }
        StringBuilder message = new StringBuilder("Parsing failed:\n");
        for (Problem problem : problems) {
            message.append(problem.toString()).append("\n");
        }
        return message.toString();
    }
}
