/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2023 The JavaParser Team.
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

package com.github.javaparser.symbolsolver;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;

class Issue3045Test extends AbstractResolutionTest {

	@Test
	void createAnonymousClassWithUnsolvableParent() {
	  String sourceCode =
			  "import com.google.common.base.Function;\n" +
	          "public class A {\n" +
	          "    private static final Function<Object, Object> MAP = new Function<Object, Object>() {\n" +
	          "        @Override\n" +
	          "        public Object apply(Object input) {\n" +
	          "            return null;\n" +
	          "        }\n" +
	          "    };\n" +
	          "}";

	  // Create the parser
	  JavaParser parser = createParserWithResolver(defaultTypeSolver());

	  // Get the method return type that is declared inside of anonymous class
	  Optional<Type> methodType = parser.parse(sourceCode)
	          .getResult()
	          .flatMap(cu -> cu.findFirst(MethodDeclaration.class))
	          .map(MethodDeclaration::getType);
	  assertTrue(methodType.isPresent());

	  // Try to resolve the given type and expect an unsolved exception
	  assertThrows(UnsolvedSymbolException.class, methodType.get()::resolve);
	}

}
