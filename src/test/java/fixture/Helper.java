/*
 * Copyright (C) 2008 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 30/06/2008
 */
package fixture;

import japa.parser.JavaParser;
import japa.parser.ParseException;
import japa.parser.ast.CompilationUnit;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

/**
 * @author Julio Vilmar Gesser
 */
final public class Helper {

	private Helper() {
		// hide the constructor
	}

	private static InputStream getInputStream(final String sourceFolder, final Class<?> clazz) {
		return clazz.getResourceAsStream("/" + clazz.getName().replace('.', '/') + ".java");
	}

	@Deprecated public static CompilationUnit parserClass(final String sourceFolder, final Class<?> clazz)
			throws ParseException {
		return JavaParser.parse(getInputStream(sourceFolder, clazz));
	}

	public static CompilationUnit parserClass(final InputStream inputStream) throws ParseException {
		return JavaParser.parse(inputStream);
	}

	public static CompilationUnit parserString(final String source) throws ParseException {
		// FIXME potential encoding bug in getBytes()
		return JavaParser.parse(new ByteArrayInputStream(source.getBytes()));
	}

	public static String readStream(final InputStream inputStream) throws IOException {
		final BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream));
		try {
			final StringBuilder ret = new StringBuilder();
			String line;
			while ((line = reader.readLine()) != null) {
				ret.append(line);
				ret.append("\n");
			}
			return ret.toString();
		} finally {
			reader.close();
		}
	}

	@Deprecated public static String readClass(final String sourceFolder, final Class<?> clazz) throws IOException {
		return readStream(getInputStream(sourceFolder, clazz));
	}

}
