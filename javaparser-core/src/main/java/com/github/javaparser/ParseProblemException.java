package com.github.javaparser;

import java.util.List;
import java.util.Optional;

import static java.util.Collections.singletonList;

/**
 * Thrown when parsing problems occur during parsing with the static methods on JavaParser.
 */
public class ParseProblemException extends RuntimeException {
	/**
	 * The problems that were encountered during parsing
	 */
	public final List<Problem> problems;

	public ParseProblemException(List<Problem> problems) {
		super(createMessage(problems));
		this.problems = problems;
	}

	public ParseProblemException(Throwable throwable) {
		this(singletonList(new Problem(throwable.getMessage(), Optional.empty(), Optional.of(throwable))));
	}

	private static String createMessage(List<Problem> problems) {
		StringBuilder message = new StringBuilder();
		for (Problem problem : problems) {
			message.append(problem.toString()).append("\n");
		}
		return message.toString();
	}
}