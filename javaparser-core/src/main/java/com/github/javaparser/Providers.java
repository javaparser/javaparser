package com.github.javaparser;

import java.io.*;
import java.nio.charset.Charset;

/**
 * Factory for providers of source code for JavaParser.
 * Providers that have no parameter for encoding but need it will use UTF-8.
 */
public abstract class Providers {
	public static final Charset UTF8 = Charset.forName("utf-8");

	private Providers() {
	}

	public static Provider provider(Reader reader) {
		return new StreamProvider(reader);
	}

	public static Provider provider(InputStream input, Charset encoding) {
		try {
			return new StreamProvider(input, encoding.name());
		} catch (IOException e) {
			// The only one that is thrown is UnsupportedCharacterEncodingException,
			// and that's a fundamental problem, so runtime exception.
			throw new RuntimeException(e);
		}
	}

	public static Provider provider(InputStream input) {
		return provider(input, UTF8);
	}

	public static Provider provider(File file, Charset encoding) throws FileNotFoundException {
		return provider(new FileInputStream(file), encoding);
	}

	public static Provider provider(File file) throws FileNotFoundException {
		return provider(file, UTF8);
	}

	public static Provider provider(String source) {
		return new StringProvider(source);
	}

}
