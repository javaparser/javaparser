package com.github.javaparser;

/**
 * A problem that was encountered during parsing.
 */
public class Problem {
    public final String message;
    public final Range range;

    Problem(String message, Range range) {
        this.message = message;
        this.range = range;
    }

    @Override
    public String toString() {
        return message + " " + range;
    }
}