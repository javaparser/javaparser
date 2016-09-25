package com.github.javaparser;

import java.util.List;

import static com.github.javaparser.utils.Utils.EOL;

/**
 * Thrown when parsing problems occur during parsing with the static methods on JavaParser.
 */
public class ParseProblemException extends RuntimeException {
    /** The problems that were encountered during parsing */
    public final List<Problem> problems;
    
    ParseProblemException(List<Problem> problems) {
        super(createMessage(problems));
        this.problems = problems;
    }
    
    private static String createMessage(List<Problem> problems){
        StringBuilder message = new StringBuilder();
        for(Problem problem: problems){
            message.append(problem.toString()).append(EOL);
        }
        return message.toString();
    }
}