package com.github.javaparser;

import java.util.List;
import java.util.Optional;

/**
 * The results given when parsing with an instance of JavaParser.
 */
public class ParseResult<T> {
    public final Optional<T> result;
    public final List<Problem> problemsList;
    public final List<Token> tokensList;

    public ParseResult(Optional<T> result, List<Problem> problemsList, List<Token> tokensList) {
        this.result = result;
        this.problemsList = problemsList;
        this.tokensList = tokensList;
    }
    
    public boolean isSuccessful() {
        return problemsList.isEmpty();
    }

    

    @Override   
    public String toString() {
        if (isSuccessful()) {
            return "Parsing successful";
        }
        StringBuilder message = new StringBuilder("Parsing failed:\n");
        for (Problem problem : problemsList) {
            message.append(problem.toString()).append("\n");
        }
        return message.toString();
    }
}
