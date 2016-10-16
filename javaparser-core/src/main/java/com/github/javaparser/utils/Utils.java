/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.utils;

import com.github.javaparser.ast.NodeList;

import java.io.IOException;
import java.io.Reader;
import java.util.*;

/**
 * Any kind of utility.
 *
 * @author Federico Tomassetti
 */
public class Utils {
	public static final String EOL = System.getProperty("line.separator");
	public static <T> List<T> ensureNotNull(List<T> list) {
		return list == null ? new ArrayList<T>() : list;
	}

	public static <E> boolean isNullOrEmpty(Collection<E> collection) {
		return collection == null || collection.isEmpty();
	}

	public static boolean isNullOrEmpty(NodeList<?> collection) {
		return collection == null || collection.isEmpty();
	}

	public static <T> T assertNotNull(T o) {
		if (o == null) {
			throw new AssertionError("A reference was unexpectedly null.");
		}
		return o;
	}

	/**
	 * @return string with ASCII characters 10 and 13 replaced by the text "\n" and "\r".
	 */
	public static String escapeEndOfLines(String string) {
		StringBuilder escapedString = new StringBuilder();
		for (char c : string.toCharArray()) {
			switch (c) {
				case '\n':
					escapedString.append("\\n");
					break;
				case '\r':
					escapedString.append("\\r");
					break;
				default:
					escapedString.append(c);
			}
		}
		return escapedString.toString();
	}

	public static String readerToString(Reader reader) throws IOException {
		final StringBuilder result = new StringBuilder();
		final char[] buffer = new char[8 * 1024];
		int numChars;

		while ((numChars = reader.read(buffer, 0, buffer.length)) > 0) {
			result.append(buffer, 0, numChars);
		}

		return result.toString();
	}

	/**
	 * Puts varargs in a mutable list.
	 * This does not have the disadvantage of Arrays#asList that it has a static size. 
	 */
	public static <T> List<T> arrayToList(T[] array){
		List<T> list = new LinkedList<>();
		Collections.addAll(list, array);
		return list;
	}

    /**
     * Scala-like statically importable shortcut to Optional.of
     */
    public static <T> Optional<T> some(T t) {
        return Optional.of(t);
    }

    /**
     * Importable shortcut to Optional.ofNullable
     */
    public static <T> Optional<T> option(T t) {
        return Optional.ofNullable(t);
    }

    /**
     * Scala-like importable shortcut to Optional.empty()
     */
    public static <T> Optional<T> none() {
        return Optional.empty();
    }
}
