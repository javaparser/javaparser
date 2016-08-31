package com.github.javaparser;

import java.util.List;
import java.util.Optional;

public class ParseResult<T> {
	public ParseResult(Optional<T> result, List<Problem> problems) {
		this.result = result;
		this.problems = problems;
	}

	public final List<Problem> problems;

	public final Optional<T> result;

	public boolean isSuccessful() {
		return problems.isEmpty();
	}
}