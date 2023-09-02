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

package com.github.javaparser.symbolsolver.javaparsermodel.declarations;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.symbolsolver.resolution.AbstractResolutionTest;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import com.github.javaparser.utils.CodeGenerationUtils;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.StaticJavaParser.parse;
import static org.junit.jupiter.api.Assertions.*;

class JavaParserAnnotationDeclarationTest extends AbstractResolutionTest {

	private final TypeSolver typeSolver = new ReflectionTypeSolver();
	private final JavaParser javaParser = createParserWithResolver(typeSolver);

	@Test
	void getAllFields_shouldReturnASingleField() {
		String sourceCode = "@interface Foo { int a = 0; }";

		ParseResult<CompilationUnit> result = javaParser.parse(sourceCode);
		assertTrue(result.getResult().isPresent());
		CompilationUnit cu = result.getResult().get();

		Optional<AnnotationDeclaration> annotation = cu.findFirst(AnnotationDeclaration.class);
		assertTrue(annotation.isPresent());

		List<ResolvedFieldDeclaration> fields = annotation.get().resolve().getAllFields();
		assertEquals(1, fields.size());
		assertEquals("a", fields.get(0).getName());
	}

	@Test
	void getAllFields_shouldReturnMultipleVariablesDeclaration() {
		String sourceCode = "@interface Foo { int a = 0, b = 1; }";

		ParseResult<CompilationUnit> result = javaParser.parse(sourceCode);
		assertTrue(result.getResult().isPresent());
		CompilationUnit cu = result.getResult().get();

		Optional<AnnotationDeclaration> annotation = cu.findFirst(AnnotationDeclaration.class);
		assertTrue(annotation.isPresent());

		List<ResolvedFieldDeclaration> fields = annotation.get().resolve().getAllFields();
		assertEquals(2, fields.size());
		assertEquals("a", fields.get(0).getName());
		assertEquals("b", fields.get(1).getName());
	}

	@Test
	void testForIssue3094() {
		String sourceCode = "@interface Foo { int a = 0; int b = a; }";
		ParseResult<CompilationUnit> result = javaParser.parse(sourceCode);
		assertTrue(result.getResult().isPresent());
		CompilationUnit cu = result.getResult().get();

		Optional<NameExpr> nameExpr = cu.findFirst(NameExpr.class);
		assertTrue(nameExpr.isPresent());
		assertDoesNotThrow(nameExpr.get()::resolve);
	}

	@Test
	void internalTypes_shouldFindAllInnerTypeDeclaration() {
		String sourceCode = "@interface Foo { class A {} interface B {} @interface C {} enum D {} }";

		ParseResult<CompilationUnit> result = javaParser.parse(sourceCode);
		assertTrue(result.getResult().isPresent());
		CompilationUnit cu = result.getResult().get();

		Optional<AnnotationDeclaration> annotation = cu.findFirst(AnnotationDeclaration.class);
		assertTrue(annotation.isPresent());
		assertEquals(4, annotation.get().resolve().internalTypes().size());
	}
	
	@Test
    void isAnnotationNotInheritable() {
        String sourceCode = "@interface Foo {}";

        ParseResult<CompilationUnit> result = javaParser.parse(sourceCode);
        assertTrue(result.getResult().isPresent());
        CompilationUnit cu = result.getResult().get();

        Optional<AnnotationDeclaration> annotation = cu.findFirst(AnnotationDeclaration.class);
        assertTrue(annotation.isPresent());

        assertFalse(annotation.get().resolve().isInheritable());
    }
	
	@Test
    void isAnnotationInheritable() {
        String sourceCode = "import java.lang.annotation.Inherited;\n" + 
                "    @Inherited\n" + 
                "    @interface Foo {}";

        ParseResult<CompilationUnit> result = javaParser.parse(sourceCode);
        assertTrue(result.getResult().isPresent());
        CompilationUnit cu = result.getResult().get();

        Optional<AnnotationDeclaration> annotation = cu.findFirst(AnnotationDeclaration.class);
        assertTrue(annotation.isPresent());

        assertTrue(annotation.get().resolve().isInheritable());
    }

	@Test
	public void checkModifiersOnAnnotation() throws IOException {
		ReflectionTypeSolver reflectionTypeSolver = new ReflectionTypeSolver();
		Path rootDir = CodeGenerationUtils.mavenModuleRoot(JavaParserFieldDeclarationTest.class).resolve("src/test/java/com/github/javaparser/symbolsolver/testingclasses");
		CompilationUnit cu1 = parse(rootDir.resolve("AnnotationWithoutModifiers.java"));

		AnnotationDeclaration tempAnnotationWithoutModifiers = cu1.findAll(AnnotationDeclaration.class).get(0);
		JavaParserAnnotationDeclaration tempResolvedAnnotationWithoutModifiers = new JavaParserAnnotationDeclaration(tempAnnotationWithoutModifiers, reflectionTypeSolver);

		assertTrue(tempResolvedAnnotationWithoutModifiers.hasModifier(Modifier.Keyword.PUBLIC));
		assertTrue(tempResolvedAnnotationWithoutModifiers.hasModifier(Modifier.Keyword.ABSTRACT));
		assertFalse(tempResolvedAnnotationWithoutModifiers.hasModifier(Modifier.Keyword.FINAL));

		CompilationUnit cu2 = parse(rootDir.resolve("AnnotationWithModifiers.java"));

		AnnotationDeclaration tempAnnotationWithModifiers = cu2.findAll(AnnotationDeclaration.class).get(0);
		JavaParserAnnotationDeclaration tempResolvedAnnotationWithModifiers = new JavaParserAnnotationDeclaration(tempAnnotationWithModifiers, reflectionTypeSolver);

		assertTrue(tempResolvedAnnotationWithModifiers.hasModifier(Modifier.Keyword.PUBLIC));
		assertTrue(tempResolvedAnnotationWithModifiers.hasModifier(Modifier.Keyword.ABSTRACT));
		assertFalse(tempResolvedAnnotationWithModifiers.hasModifier(Modifier.Keyword.FINAL));
	}
}
