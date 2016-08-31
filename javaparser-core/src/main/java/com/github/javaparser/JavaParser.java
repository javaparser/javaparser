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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.Statement;

import java.io.*;
import java.nio.charset.Charset;
import java.util.List;
import java.util.Optional;

import static com.github.javaparser.ASTParser.tokenRange;
import static com.github.javaparser.Providers.UTF8;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.Utils.providerToString;
import static java.util.Collections.singletonList;

/**
 * Parse Java source code and creates Abstract Syntax Trees.
 *
 * @author Júlio Vilmar Gesser
 */
public final class JavaParser {
	private final CommentsInserter commentsInserter;

	private ASTParser astParser = null;

	/**
	 * Instantiate the parser. Note that parsing can also be done with the static methods on this class.
	 * Creating an instance will reduce setup time between parsing files.
	 */
	public JavaParser(ParserConfiguration configuration) {
		commentsInserter = new CommentsInserter(configuration);
	}

	private ASTParser getParserForProvider(Provider provider) {
		if (astParser == null) {
			astParser = new ASTParser(provider);
		} else {
			astParser.ReInit(provider);
		}
		return astParser;
	}

	/**
	 * Return the list of tokens that have been encountered while parsing code
	 * using this parser.
	 *
	 * @return a list of tokens
	 */
	public List<Token> getTokens() {
		if (astParser == null) {
			throw new IllegalStateException("Don't ask for tokens before anything has been parsed.");
		}
		return astParser.getTokens();
	}

	/**
	 * Parses source code without comments.
	 * It takes the source code from a Provider.
	 * The context indicates what can be found in the source code (compilation unit, block, import...)
	 *
	 * @param context  refer to the constants in ParseContext to see what can be parsed.
	 * @param provider refer to Providers to see how you can read source
	 * @param <N>      the subclass of Node that is the result of parsing in the context.
	 * @return the parse result and a collection of encountered problems.
	 */
	public <N> ParseResult<N> parseStructure(ParseContext<N> context, Provider provider) {
		final ASTParser parser = getParserForProvider(provider);
		try {
			N resultNode = context.parse(parser);
			return new ParseResult<>(Optional.of(resultNode), parser.problems);
		} catch (ParseException e) {
			return new ParseResult<>(Optional.empty(), singletonList(new Problem(e.getMessage(), tokenRange(e.currentToken))));
        } catch (TokenMgrException e) {
            return new ParseResult<>(Optional.empty(), singletonList(new Problem(e.getMessage(), Range.UNKNOWN)));
		} finally {
			try {
				provider.close();
			} catch (IOException e) {
				// Since we're done parsing and have our result, we don't care about any errors.
			}
		}
	}

	/**
	 * Parses a compilation unit and its comments.
	 * It takes the source code from a Provider.
	 *
	 * @param provider refer to Providers to see how you can read source
	 * @return the parse result and a collection of encountered problems.
	 */
	public ParseResult<CompilationUnit> parseFull(Provider provider) {
		try {
			final String sourceCode = providerToString(provider);
            final ASTParser parser = getParserForProvider(provider(sourceCode));
			final CompilationUnit resultNode = ParseContext.COMPILATION_UNIT.parse(parser);
			commentsInserter.insertComments(resultNode, sourceCode);

			return new ParseResult<>(Optional.of(resultNode), parser.problems);
		} catch (ParseException e) {
            return new ParseResult<>(Optional.empty(), singletonList(new Problem(e.getMessage(), tokenRange(e.currentToken))));
        } catch (TokenMgrException e) {
            return new ParseResult<>(Optional.empty(), singletonList(new Problem(e.getMessage(), Range.UNKNOWN)));
        } catch (IOException e) {
            // The commentsInserter won't throw an IOException since it's reading from a String.
			throw new AssertionError("Unreachable code");
		} finally {
			try {
				provider.close();
			} catch (IOException e) {
				// Since we're done parsing and have our result, we don't care about any errors.
			}
		}
	}

	public static CompilationUnit parse(final InputStream in, final Charset encoding) throws ParseProblemException {
		return parse(in, encoding, true);
	}

	/**
	 * Parses the Java code contained in the {@link InputStream} and returns a
	 * {@link CompilationUnit} that represents it.
	 *
	 * @param in       {@link InputStream} containing Java source code
	 * @param encoding encoding of the source code
	 * @return CompilationUnit representing the Java source code
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static CompilationUnit parse(final InputStream in, Charset encoding, boolean considerComments) throws ParseProblemException {
		return simplifiedParse(provider(in, encoding), considerComments);
	}

	/**
	 * Parses the Java code contained in the {@link InputStream} and returns a
	 * {@link CompilationUnit} that represents it.<br>
	 * Note: Uses UTF-8 encoding
	 *
	 * @param in {@link InputStream} containing Java source code
	 * @return CompilationUnit representing the Java source code
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static CompilationUnit parse(final InputStream in) throws ParseProblemException {
		return parse(in, UTF8, true);
	}

	public static CompilationUnit parse(final File file, final Charset encoding) throws ParseProblemException, FileNotFoundException {
		return simplifiedParse(provider(file, encoding), true);
	}

	/**
	 * Parses the Java code contained in a {@link File} and returns a
	 * {@link CompilationUnit} that represents it.
	 *
	 * @param file     {@link File} containing Java source code
	 * @param encoding encoding of the source code
	 * @return CompilationUnit representing the Java source code
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static CompilationUnit parse(final File file, final Charset encoding, boolean considerComments) throws ParseProblemException, FileNotFoundException {
		return simplifiedParse(provider(file, encoding), considerComments);
	}

	/**
	 * Parses the Java code contained in a {@link File} and returns a
	 * {@link CompilationUnit} that represents it.<br>
	 * Note: Uses UTF-8 encoding
	 *
	 * @param file {@link File} containing Java source code
	 * @return CompilationUnit representing the Java source code
	 * @throws ParseProblemException if the source code has parser errors
	 * @throws FileNotFoundException the file was not found
	 */
	public static CompilationUnit parse(final File file) throws FileNotFoundException, ParseProblemException {
		return simplifiedParse(provider(file), true);
	}

	public static CompilationUnit parse(final Reader reader) throws ParseProblemException {
		return parse(reader, true);
	}

	public static CompilationUnit parse(final Reader reader, boolean considerComments) throws ParseProblemException {
		return simplifiedParse(provider(reader), considerComments);
	}

	/**
	 * Parses the Java code contained in code and returns a
	 * {@link CompilationUnit} that represents it.
	 *
	 * @param code             Java source code
	 * @param considerComments parse or ignore comments
	 * @return CompilationUnit representing the Java source code
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static CompilationUnit parse(String code, boolean considerComments) throws ParseProblemException {
		return simplifiedParse(provider(code), considerComments);
	}

	/**
	 * Parses the Java code contained in code and returns a
	 * {@link CompilationUnit} that represents it.
	 *
	 * @param code Java source code
	 * @return CompilationUnit representing the Java source code
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static CompilationUnit parse(String code) throws ParseProblemException {
		return parse(code, true);
	}

	/**
	 * Parses the Java block contained in a {@link String} and returns a
	 * {@link BlockStmt} that represents it.
	 *
	 * @param blockStatement {@link String} containing Java block code
	 * @return BlockStmt representing the Java block
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static BlockStmt parseBlock(final String blockStatement) throws ParseProblemException {
		return simplifiedParse(ParseContext.BLOCK, provider(blockStatement));
	}

	/**
	 * Parses the Java statement contained in a {@link String} and returns a
	 * {@link Statement} that represents it.
	 *
	 * @param statement {@link String} containing Java statement code
	 * @return Statement representing the Java statement
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static Statement parseStatement(final String statement) throws ParseProblemException {
		return simplifiedParse(ParseContext.STATEMENT, provider(statement));
	}

	private static <T> T simplifiedParse(ParseContext<T> context, Provider provider) throws ParseProblemException {
		ParseResult<T> result = new JavaParser(new ParserConfiguration()).parseStructure(context, provider);
		if (result.isSuccessful()) {
			return result.result.get();
		}
		throw new ParseProblemException(result.problems);
	}

    private static CompilationUnit simplifiedParse(Provider provider, boolean considerComments) throws ParseProblemException {
        final ParseResult<CompilationUnit> result;
        if (considerComments) {
            result = new JavaParser(new ParserConfiguration()).parseFull(provider);
        } else {
            result = new JavaParser(new ParserConfiguration()).parseStructure(ParseContext.COMPILATION_UNIT, provider);
        }
        if (result.isSuccessful()) {
            return result.result.get();
        }
        throw new ParseProblemException(result.problems);
    }

	/**
	 * Parses the Java statements contained in a {@link String} and returns a
	 * list of {@link Statement} that represents it.
	 *
	 * @param statements {@link String} containing Java statements
	 * @return list of Statement representing the Java statement
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static List<Statement> parseStatements(final String statements) throws ParseProblemException {
		return simplifiedParse(ParseContext.STATEMENTS, provider(statements));
	}

	/**
	 * Parses the Java import contained in a {@link String} and returns a
	 * {@link ImportDeclaration} that represents it.
	 *
	 * @param importDeclaration {@link String} containing Java import code
	 * @return ImportDeclaration representing the Java import declaration
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static ImportDeclaration parseImport(final String importDeclaration) throws ParseProblemException {
		return simplifiedParse(ParseContext.IMPORT_DECLARATION, provider(importDeclaration));
	}

	/**
	 * Parses the Java expression contained in a {@link String} and returns a
	 * {@link Expression} that represents it.
	 *
	 * @param expression {@link String} containing Java expression
	 * @return Expression representing the Java expression
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static Expression parseExpression(final String expression) throws ParseProblemException {
		return simplifiedParse(ParseContext.EXPRESSION, provider(expression));
	}

	/**
	 * Parses the Java annotation contained in a {@link String} and returns a
	 * {@link AnnotationExpr} that represents it.
	 *
	 * @param annotation {@link String} containing Java annotation
	 * @return AnnotationExpr representing the Java annotation
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static AnnotationExpr parseAnnotation(final String annotation) throws ParseProblemException {
		return simplifiedParse(ParseContext.ANNOTATION, provider(annotation));
	}

	/**
	 * Parses the Java annotation body declaration(e.g fields or methods) contained in a
	 * {@link String} and returns a {@link BodyDeclaration} that represents it.
	 *
	 * @param body {@link String} containing Java body declaration
	 * @return BodyDeclaration representing the Java annotation
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static BodyDeclaration<?> parseAnnotationBodyDeclaration(final String body) throws ParseProblemException {
		return simplifiedParse(ParseContext.ANNOTATION_BODY, provider(body));
	}

	/**
	 * Parses a Java class body declaration(e.g fields or methods) and returns a
	 * {@link BodyDeclaration} that represents it.
	 *
	 * @param body the body of a class
	 * @return BodyDeclaration representing the Java class body
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static BodyDeclaration<?> parseClassBodyDeclaration(String body) throws ParseProblemException {
		return simplifiedParse(ParseContext.CLASS_BODY, provider(body));
	}

	/**
	 * Parses a Java interface body declaration(e.g fields or methods) and returns a
	 * {@link BodyDeclaration} that represents it.
	 *
	 * @param body the body of an interface
	 * @return BodyDeclaration representing the Java interface body
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public static BodyDeclaration parseInterfaceBodyDeclaration(String body) throws ParseProblemException {
		return simplifiedParse(ParseContext.INTERFACE_BODY, provider(body));
	}
}
