package com.github.javaparser;

public class Problem {
	public final String message;
	public final Range range;

	public Problem(String message, Range range) {
		this.message = message;
		this.range = range;
	}

	@Override
	public String toString() {
		return message + " " + range;
	}
}