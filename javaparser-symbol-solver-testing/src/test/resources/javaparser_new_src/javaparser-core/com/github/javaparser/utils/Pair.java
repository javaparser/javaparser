package com.github.javaparser.utils;

/**
 * Simply a pair of objects.
 * @param <A> type of object a.
 * @param <B> type of object b.
 */
public class Pair<A, B> {
	public final A a;
	public final B b;

	public Pair(A a, B b) {
		this.a = a;
		this.b = b;
	}
}
