/*
 * Copyright (C) 2019 The JavaParser Team.
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
package com.github.javaparser;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;

import org.junit.jupiter.api.Test;

/**
 * Test case for {@link UnicodeEscapeProcessingProvider}.
 */
public class UnicodeEscapeProcessingProviderTest {

	@Test
	void testUnicodeEscape() throws IOException {
		assertEquals("13" + '\u12aA' + "98", new String(read("13\\u12aA98")));
	}

	@Test
	void testEscapedUnicodeEscape() throws IOException {
		assertEquals("13\\\\u12aA98", new String(read("13\\\\u12aA98")));
	}
	
	@Test
	void testUnicodeEscapeWithMultipleUs() throws IOException {
		assertEquals("13" + '\u12aA' + "98", new String(read("13\\uuuuuu12aA98")));
	}
	
	@Test
	void testInputEndingInBackslash() throws IOException {
		assertEquals("foobar\\", new String(read("foobar\\")));
	}
	
	@Test
	void testInputEndingInBackslashU() throws IOException {
		assertEquals("foobar\\u", new String(read("foobar\\u")));
	}
	
	@Test
	void testInputEndingInBackslashUs() throws IOException {
		assertEquals("foobar\\uuuuuu", new String(read("foobar\\uuuuuu")));
	}
	
	@Test
	void testInputEndingInBackslashU1() throws IOException {
		assertEquals("foobar\\uA", new String(read("foobar\\uA")));
	}
	
	@Test
	void testInputEndingInBackslashU2() throws IOException {
		assertEquals("foobar\\uAB", new String(read("foobar\\uAB")));
	}
	
	@Test
	void testInputEndingInBackslashU3() throws IOException {
		assertEquals("foobar\\uABC", new String(read("foobar\\uABC")));
	}
	
	@Test
	void testInputEndingUnicodeEscape() throws IOException {
		assertEquals("foobar\uABCD", new String(read("foobar\\uABCD")));
	}
	
	@Test
	void testEmptyInput() throws IOException {
		assertEquals("", new String(read("")));
	}

	@Test
	void testBadUnicodeEscape0() throws IOException {
		assertEquals("13\\ux", new String(read("13\\ux")));
	}
	
	@Test
	void testBadUnicodeEscape1() throws IOException {
		assertEquals("13\\u1x", new String(read("13\\u1x")));
	}

	@Test
	void testBadUnicodeEscape2() throws IOException {
		assertEquals("13\\u1Ax", new String(read("13\\u1Ax")));
	}

	@Test
	void testBadUnicodeEscape3() throws IOException {
		assertEquals("13\\u1ABx", new String(read("13\\u1ABx")));
	}

	@Test
	void testBadUnicodeEscapeMultipleUs() throws IOException {
		assertEquals("13\\uuuuuu1ABx", new String(read("13\\uuuuuu1ABx")));
	}

	@Test
	void testPushBackWithFullBuffer() throws IOException {
		assertEquals("12345678\\uuxxxxxxxxxxxxxxxxxxxxxxx", new String(read("12345678\\uuxxxxxxxxxxxxxxxxxxxxxxx")));
	}
	
	@Test
	void testPushBackWithBufferShift() throws IOException {
		assertEquals("12345678\\uuxx", new String(read("12345678\\uuxx")));
	}
	
	static String read(String source) throws IOException {
		return process(provider(source));
	}

	static UnicodeEscapeProcessingProvider provider(String source) {
		UnicodeEscapeProcessingProvider provider = new UnicodeEscapeProcessingProvider(10, 
				new StringProvider(source));
		return provider;
	}

	static String process(UnicodeEscapeProcessingProvider provider)
			throws IOException {
		StringBuilder result = new StringBuilder();
		char[] buffer = new char[10];
		while (true) {
			int direct = provider.read(buffer, 0, buffer.length);
			if (direct < 0) {
				break;
			}
			result.append(buffer, 0, direct);
		}
		
		provider.close();
	
		return result.toString();
	}
}
