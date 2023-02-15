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

package com.github.javaparser.generator.core.quality;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.utils.SourceRoot;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

class NotNullGeneratorTest {

	@Test
	void testExecutionOfGenerator() throws Exception {

		// Setup the
		String resourcesFolderPath = getClass().getCanonicalName().replace(".", File.separator);

		String basePath = Paths.get("src", "test", "resources").toString();
		Path originalFile = Paths.get(basePath, resourcesFolderPath, "original");
		Path expectedFile = Paths.get(basePath, resourcesFolderPath, "expected");

		SourceRoot originalSources = new SourceRoot(originalFile);
		SourceRoot expectedSources = new SourceRoot(expectedFile);
		expectedSources.tryToParse();

		// Generate the information
		new NotNullGenerator(originalSources).generate();

		List<CompilationUnit> editedSourceCus = originalSources.getCompilationUnits();
		List<CompilationUnit> expectedSourcesCus = expectedSources.getCompilationUnits();
		assertEquals(expectedSourcesCus.size(), editedSourceCus.size());

		// Check if all the files match the expected result
		for (int i = 0 ; i < editedSourceCus.size() ; i++) {

			DefaultPrettyPrinter printer = new DefaultPrettyPrinter();
			String expectedCode = printer.print(expectedSourcesCus.get(i));
			String editedCode = printer.print(editedSourceCus.get(i));

			if (!expectedCode.equals(editedCode)) {
				System.out.println("Expected:");
				System.out.println("####");
				System.out.println(expectedSourcesCus.get(i));
				System.out.println("####");
				System.out.println("Actual:");
				System.out.println("####");
				System.out.println(editedSourceCus.get(i));
				System.out.println("####");
				fail("Actual code doesn't match with the expected code.");
			}
		}
	}

}
