package com.github.javaparser;

import java.util.List;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.EOL;

/**
 * The results given when parsing with an instance of JavaParser.
 */
public class ParseResult<T> {
    public final Optional<T> result;
    public final List<Problem> problems;
    public final List<Token> tokens;

    public ParseResult(Optional<T> result, List<Problem> problems, List<Token> tokens) {
        this.result = result;
        this.problems = problems;
        this.tokens = tokens;
    }
    
    public boolean isSuccessful() {
        return problems.isEmpty();
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
