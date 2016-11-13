package com.github.javaparser;

import java.util.List;

/**
 * Thrown when parsing problemsList occur during parsing with the static methods on JavaParser.
 */
public class ParseProblemException extends RuntimeException {
    /** The problemsList that were encountered during parsing */
    public final List<Problem> problemsList;
    
    ParseProblemException(List<Problem> problemsList) {
        super(createMessage(problemsList));
        this.problemsList = problemsList;
    }
    
    private static String createMessage(List<Problem> problemsList){
        StringBuilder message = new StringBuilder();
        for(Problem problem: problemsList){
            message.append(problem.toString()).append("\n");
        }
        return message.toString();
    }
}
