package com.github.javaparser;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A problem that was encountered during parsing.
 */
public class Problem {
    private final String message;
    private final Optional<Range> range;
    private final Optional<Throwable> cause;

    Problem(String message, Optional<Range> range, Optional<Throwable> cause) {
        this.message = assertNotNull(message);
        this.range = assertNotNull(range);
        this.cause = assertNotNull(cause);
    }

    @Override
    public String toString() {
        StringBuilder str = new StringBuilder(message);
        range.ifPresent(r -> str.append(" ").append(r));
        return str.toString();
    }

    public String getMessage() {
        return message;
    }

    public Optional<Range> getRange() {
        return range;
    }

    public Optional<Throwable> getCause() {
        return cause;
    }
}
