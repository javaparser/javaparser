package com.github.javaparser;

import java.util.Optional;

/**
 * A problem that was encountered during parsing.
 */
public class Problem {
    private final String message;
    private final Range range;
    private final Throwable cause;

    Problem(String message, Range range, Throwable cause) {
        this.message = message;
        this.range = range;
        this.cause = cause;
    }

    @Override
    public String toString() {
        StringBuilder str = new StringBuilder(message);
        if (range != null)
            str.append(" ").append(range);
        if (cause != null) {
            str.append(System.lineSeparator()).append("Problem stacktrace : ").append(System.lineSeparator());
            for (int i = 0; i < cause.getStackTrace().length; i++) {
                StackTraceElement ste = cause.getStackTrace()[i];
                str.append("  ").append(ste.toString());
                if (i + 1 != cause.getStackTrace().length)
                    str.append(System.lineSeparator());
            }
        }
        return str.toString();
    }

    public String getMessage() {
        return message;
    }

    public Optional<Range> getRange() {
        return Optional.ofNullable(range);
    }

    public Optional<Throwable> getCause() {
        return Optional.ofNullable(cause);
    }
}
