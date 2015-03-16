package com.acme;

import java.util.List;

public class TestClass {
	public static String method1(List<String>strings) {
		StringBuilder buffer = new StringBuilder();
		for (String string : strings) {
			buffer.append(string);
		}
		return buffer.toString();
	}
}
