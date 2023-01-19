/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

package com.github.javaparser.printer.lexicalpreservation;

import static com.github.javaparser.utils.TestUtils.assertEqualsStringIgnoringEol;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.body.FieldDeclaration;

public class Issue3796Test extends AbstractLexicalPreservingTest {

	@Test
    void test() {
		considerCode(
				"public class MyClass {\n"
				+ "	/** Comment */ \n"
				+ "	@Rule String s0; \n"
				+ "}");
		String expected = 
				"public class MyClass {\n" +
				"\n" +
				"}";

		List<FieldDeclaration> fields = cu.findAll(FieldDeclaration.class);
		FieldDeclaration field = fields.get(0);

		field.remove();

		assertEqualsStringIgnoringEol(expected, LexicalPreservingPrinter.print(cu));
    }
}
