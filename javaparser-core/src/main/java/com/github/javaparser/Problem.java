package com.github.javaparser;

import java.util.Optional;

/**
 * A problem that was encountered during parsing.
 */
public class Problem {
	public final String message;
	public final Optional<Range> range;
	public final Optional<Throwable> cause;

	Problem(String message, Optional<Range> range, Optional<Throwable> cause) {
		this.message = message;
		this.range = range;
		this.cause = cause;
	}

	@Override
	public String toString() {
		StringBuilder str = new StringBuilder(message);
		range.ifPresent(r -> str.append(" ").append(r));
		return str.toString();
	}
}