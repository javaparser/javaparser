/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class SimpleJavaParserTest {

	private SimpleJavaParser parser;
	private JavaParser innerParser;

	@BeforeEach
	void setup() {
		ParserConfiguration configuration = new ParserConfiguration();
		configuration.setLanguageLevel(BLEEDING_EDGE);

		innerParser = spy(new JavaParser(configuration));
		parser = spy(new SimpleJavaParser(innerParser));
	}

	@Test
	void testIfConfigurationIsAppliedProperly() {
		ParserConfiguration parserConfiguration = new ParserConfiguration();
		SimpleJavaParser simpleParser = new SimpleJavaParser(parserConfiguration);
		assertEquals(parserConfiguration, simpleParser.getWrappedParser().getParserConfiguration());
	}

	@Test
	void getWrappedParserIsAlwaysTheSame() {
		assertSame(parser.getWrappedParser(), parser.getWrappedParser(),
				"When getWrappedParser is called, should always return the same instance.");
	}

	@Test
	void parseWithInputStream() {
		String sourceCode = "class A {}";
		InputStream byteArrayInput = new ByteArrayInputStream(sourceCode.getBytes());
		assertNotNull(parser.parse(byteArrayInput));

		verify(parser, times(1)).parse(byteArrayInput);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parse(byteArrayInput);
	}

	@Test
	void parseWithPath() throws IOException {
		Path path = Files.createTempFile("", "");
		assertNotNull(parser.parse(path));

		verify(parser, times(1)).parse(path);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parse(path);
	}

	@Test
	void parseWithFile() throws IOException {
		File file = Files.createTempFile("", "").toFile();
		assertNotNull(parser.parse(file));

		verify(parser, times(1)).parse(file);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parse(file);
	}

	@Test
	void parseWithReader() {
		Reader reader = new StringReader("class A {}");
		assertNotNull(parser.parse(reader));

		verify(parser, times(1)).parse(reader);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parse(reader);
	}

	@Test
	void parseWithSourceCode() {
		String sourceCode = "class A {}";
		assertNotNull(parser.parse(sourceCode));

		verify(parser, times(1)).parse(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parse(sourceCode);
	}

	@Test
	void parserBlockWithSourceCode() {
		String sourceCode = "{}";
		assertNotNull(parser.parseBlock(sourceCode));

		verify(parser, times(1)).parseBlock(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseBlock(sourceCode);
	}

	@Test
	void parseStatementWithSourceCode() {
		String sourceCode = "int i = 0;";
		assertNotNull(parser.parseStatement(sourceCode));

		verify(parser, times(1)).parseStatement(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseStatement(sourceCode);
	}

	@Test
	void parseImportWithSourceCode() {
		String sourceCode = "import com.example.Clazz;";
		assertNotNull(parser.parseImport(sourceCode));

		verify(parser, times(1)).parseImport(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseImport(sourceCode);
	}

	@Test
	void parseExpressionWithSourceCode() {
		String sourceCode = "true";
		assertNotNull(parser.parseExpression(sourceCode));

		verify(parser, times(1)).parseExpression(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseExpression(sourceCode);
	}

	@Test
	void parseAnnotationWithSourceCode() {
		String sourceCode = "@Test";
		assertNotNull(parser.parseAnnotation(sourceCode));

		verify(parser, times(1)).parseAnnotation(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseAnnotation(sourceCode);
	}

	@Test
	void parseAnnotationBodyDeclarationWithSourceCode() {
		String sourceCode = "@interface Test {}";
		assertNotNull(parser.parseAnnotationBodyDeclaration(sourceCode));

		verify(parser, times(1)).parseAnnotationBodyDeclaration(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseAnnotationBodyDeclaration(sourceCode);
	}

	@Test
	void parseBodyDeclarationWithSourceCode() {
		String sourceCode = "{}";
		assertNotNull(parser.parseBodyDeclaration(sourceCode));

		verify(parser, times(1)).parseBodyDeclaration(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseBodyDeclaration(sourceCode);
	}

	@Test
	void parseClassOrInterfaceTypeWithSourceCode() {
		String sourceCode = "Object";
		assertNotNull(parser.parseClassOrInterfaceType(sourceCode));

		verify(parser, times(1)).parseClassOrInterfaceType(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseClassOrInterfaceType(sourceCode);
	}

	@Test
	void parseTypeWithSourceCode() {
		String sourceCode = "Object";
		assertNotNull(parser.parseType(sourceCode));

		verify(parser, times(1)).parseType(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseType(sourceCode);
	}

	@Test
	void parseVariableDeclarationExprWithSourceCode() {
		String sourceCode = "int i = 0";
		assertNotNull(parser.parseVariableDeclarationExpr(sourceCode));

		verify(parser, times(1)).parseVariableDeclarationExpr(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseVariableDeclarationExpr(sourceCode);
	}

	@Test
	void parseJavaDocWithSourceCode() {
		String javaDoc = "/**\n" +
				"\t * Simple JavaDoc\n" +
				"\t */";
		assertNotNull(parser.parseJavadoc(javaDoc));

		verify(parser, times(1)).parseJavadoc(javaDoc);
		verifyNoMoreInteractions(parser);
		verifyNoInteractions(innerParser);
	}

	@Test
	void parseExplicitConstructorInvocationStmtWithSourceCode() {
		String sourceCode = "super();";
		assertNotNull(parser.parseExplicitConstructorInvocationStmt(sourceCode));

		verify(parser, times(1)).parseExplicitConstructorInvocationStmt(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseExplicitConstructorInvocationStmt(sourceCode);
	}

	@Test
	void parseNameWithSourceCode() {
		String sourceCode = "java.lang.Integer";
		assertNotNull(parser.parseName(sourceCode));

		verify(parser, times(1)).parseName(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseName(sourceCode);
	}

	@Test
	void parseSimpleNameWithSourceCode() {
		String sourceCode = "Integer";
		assertNotNull(parser.parseSimpleName(sourceCode));

		verify(parser, times(1)).parseSimpleName(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseSimpleName(sourceCode);
	}

	@Test
	void parseParameterWithSourceCode() {
		String sourceCode = "Integer param";
		assertNotNull(parser.parseParameter(sourceCode));

		verify(parser, times(1)).parseParameter(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseParameter(sourceCode);
	}

	@Test
	void parsePackageDeclarationWithSourceCode() {
		String sourceCode = "package com.example;";
		assertNotNull(parser.parsePackageDeclaration(sourceCode));

		verify(parser, times(1)).parsePackageDeclaration(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parsePackageDeclaration(sourceCode);
	}

	@Test
	void parseTypeDeclarationWithSourceCode() {
		String sourceCode = "class A {}";
		assertNotNull(parser.parseTypeDeclaration(sourceCode));

		verify(parser, times(1)).parseTypeDeclaration(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseTypeDeclaration(sourceCode);
	}

	@Test
	void parseModuleDeclarationWithSourceCode() {
		String sourceCode = "@Foo module com.github.abc { requires a.B; }";
		assertNotNull(parser.parseModuleDeclaration(sourceCode));

		verify(parser, times(1)).parseModuleDeclaration(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseModuleDeclaration(sourceCode);
	}

	@Test
	void parseModuleDirectiveWithSourceCode() {
		String sourceCode = "opens C;";
		assertNotNull(parser.parseModuleDirective(sourceCode));

		verify(parser, times(1)).parseModuleDirective(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseModuleDirective(sourceCode);
	}

	@Test
	void parseTypeParameterWithSourceCode() {
		String sourceCode = "T extends Serializable";
		assertNotNull(parser.parseTypeParameter(sourceCode));

		verify(parser, times(1)).parseTypeParameter(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseTypeParameter(sourceCode);
	}

	@Test
	void parseMethodDeclarationWithSourceCode() {
		String sourceCode = "void foo() {}";
		assertNotNull(parser.parseMethodDeclaration(sourceCode));

		verify(parser, times(1)).parseMethodDeclaration(sourceCode);
		verify(parser, times(1)).getWrappedParser();
		verifyNoMoreInteractions(parser);

		verify(innerParser, times(1)).parseMethodDeclaration(sourceCode);
	}

}
