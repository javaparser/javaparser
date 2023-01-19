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

package com.github.javaparser.symbolsolver;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class Issue3099Test extends AbstractResolutionTest {

	@Test
	void illegalArgumentExceptionWhenSolvingName() throws IOException {

		// Setup symbol solver
		JavaParserTypeSolver javaParserTypeSolver = new JavaParserTypeSolver(adaptPath("src/test/resources/issue3099/"));
		StaticJavaParser.getConfiguration()
				.setSymbolResolver(new JavaSymbolSolver(
						new CombinedTypeSolver(new ReflectionTypeSolver(), javaParserTypeSolver))
				);

		// Parse the File
		Path filePath = adaptPath("src/test/resources/issue3099/com/example/Beta.java");
		CompilationUnit cu = StaticJavaParser.parse(filePath);

		// Get the expected inner class
		List<ClassOrInterfaceDeclaration> classes = cu.findAll(ClassOrInterfaceDeclaration.class);
		assertEquals(2, classes.size());
		ResolvedReferenceTypeDeclaration innerInterface = classes.get(1).resolve();
		assertTrue(innerInterface.isInterface());

		// Check if the value is present
		Optional<ResolvedReferenceType> resolvedType = cu.findFirst(VariableDeclarator.class)
				.map(VariableDeclarator::getType)
				.map(Type::resolve)
				.filter(ResolvedType::isReferenceType)
				.map(ResolvedType::asReferenceType);
		assertTrue(resolvedType.isPresent());
		assertEquals(innerInterface, resolvedType.get().getTypeDeclaration().orElse(null));
	}

}
