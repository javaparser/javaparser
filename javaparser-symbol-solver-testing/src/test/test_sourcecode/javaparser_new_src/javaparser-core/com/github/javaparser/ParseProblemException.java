package com.github.javaparser;

import java.util.List;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;
import static java.util.Collections.singletonList;

import static com.github.javaparser.utils.Utils.EOL;

/**
 * Thrown when parsing problems occur during parsing with the static methods on JavaParser.
 */
public class ParseProblemException extends RuntimeException {
    /**
     * The problems that were encountered during parsing
     */
    private final List<Problem> problems;

    ParseProblemException(List<Problem> problems) {
        super(createMessage(assertNotNull(problems)));
        this.problems = problems;
    }

    ParseProblemException(Throwable throwable) {
        this(singletonList(new Problem(throwable.getMessage(), Optional.empty(), Optional.of(throwable))));
    }

    private static String createMessage(List<Problem> problems) {
        StringBuilder message = new StringBuilder();
        for(Problem problem: problems){
            message.append(problem.toString()).append(EOL);
        }
        return message.toString();
    }

    public List<Problem> getProblems() {
        return problems;
    }
}
