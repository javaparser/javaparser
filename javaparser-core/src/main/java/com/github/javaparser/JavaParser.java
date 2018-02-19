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
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.javadoc.Javadoc;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.Path;

import static com.github.javaparser.ParseStart.*;
import static com.github.javaparser.Problem.PROBLEM_BY_BEGIN_POSITION;
import static com.github.javaparser.Providers.*;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * Parse Java source code and creates Abstract Syntax Trees.
 *
 * @author Júlio Vilmar Gesser
 */
public final class JavaParser {
    private final ParserConfiguration configuration;

    private GeneratedJavaParser astParser = null;
    private static ParserConfiguration staticConfiguration = new ParserConfiguration();

    /**
     * Instantiate the parser with default configuration. Note that parsing can also be done with the static methods on
     * this class.
     * Creating an instance will reduce setup time between parsing files.
     */
    public JavaParser() {
        this(new ParserConfiguration());
    }

    /**
     * Instantiate the parser. Note that parsing can also be done with the static methods on this class.
     * Creating an instance will reduce setup time between parsing files.
     */
    public JavaParser(ParserConfiguration configuration) {
        this.configuration = configuration;
    }

    /**
     * Get the configuration for the static parse... methods.
     * This is a STATIC field, so modifying it will directly change how all static parse... methods work!
     */
    public static ParserConfiguration getStaticConfiguration() {
        return staticConfiguration;
    }

    /**
     * Set the configuration for the static parse... methods.
     * This is a STATIC field, so modifying it will directly change how all static parse... methods work!
     */
    public static void setStaticConfiguration(ParserConfiguration staticConfiguration) {
        JavaParser.staticConfiguration = staticConfiguration;
    }

    /**
     * Get the non-static configuration for this parser.
     *
     * @return The non-static configuration for this parser.
     */
    public ParserConfiguration getParserConfiguration() {
        return this.configuration;
    }

    private GeneratedJavaParser getParserForProvider(Provider provider) {
        if (astParser == null) {
            astParser = new GeneratedJavaParser(provider);
        } else {
            astParser.reset(provider);
        }
        astParser.setTabSize(configuration.getTabSize());
        astParser.setStoreTokens(configuration.isStoreTokens());
        return astParser;
    }

    /**
     * Parses source code.
     * It takes the source code from a Provider.
     * The start indicates what can be found in the source code (compilation unit, block, import...)
     *
     * @param start refer to the constants in ParseStart to see what can be parsed.
     * @param provider refer to Providers to see how you can read source. The provider will be closed after parsing.
     * @param <N> the subclass of Node that is the result of parsing in the start.
     * @return the parse result, a collection of encountered problems, and some extra data.
     */
    public <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider) {
        assertNotNull(start);
        assertNotNull(provider);
        final GeneratedJavaParser parser = getParserForProvider(provider);
        try {
            N resultNode = start.parse(parser);
            ParseResult<N> result = new ParseResult<>(resultNode, parser.problems, parser.getTokens(),
                    parser.getCommentsCollection());

            configuration.getPostProcessors().forEach(postProcessor ->
                    postProcessor.process(result, configuration));

            result.getProblems().sort(PROBLEM_BY_BEGIN_POSITION);

            return result;
        } catch (Exception e) {
            final String message = e.getMessage() == null ? "Unknown error" : e.getMessage();
            parser.problems.add(new Problem(message, null, e));
            return new ParseResult<>(null, parser.problems, parser.getTokens(), parser.getCommentsCollection());
        } finally {
            try {
                provider.close();
            } catch (IOException e) {
                // Since we're done parsing and have our result, we don't care about any errors.
            }
        }
    }

    /**
     * Parses the Java code contained in the {@link InputStream} and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param in {@link InputStream} containing Java source code. It will be closed after parsing.
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(final InputStream in, Charset encoding) {
        return simplifiedParse(COMPILATION_UNIT, provider(in, encoding));
    }

    /**
     * Parses the Java code contained in the {@link InputStream} and returns a
     * {@link CompilationUnit} that represents it.<br>
     * Note: Uses UTF-8 encoding
     *
     * @param in {@link InputStream} containing Java source code. It will be closed after parsing.
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(final InputStream in) {
        return parse(in, UTF8);
    }

    /**
     * Parses the Java code contained in a {@link File} and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param file {@link File} containing Java source code. It will be closed after parsing.
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws FileNotFoundException the file was not found
     */
    public static CompilationUnit parse(final File file, final Charset encoding) throws FileNotFoundException {
        return simplifiedParse(COMPILATION_UNIT, provider(file, encoding)).setStorage(file.toPath());
    }

    /**
     * Parses the Java code contained in a {@link File} and returns a
     * {@link CompilationUnit} that represents it.<br>
     * Note: Uses UTF-8 encoding
     *
     * @param file {@link File} containing Java source code. It will be closed after parsing.
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws FileNotFoundException the file was not found
     */
    public static CompilationUnit parse(final File file) throws FileNotFoundException {
        return simplifiedParse(COMPILATION_UNIT, provider(file)).setStorage(file.toPath());
    }

    /**
     * Parses the Java code contained in a file and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param path path to a file containing Java source code
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws IOException the path could not be accessed
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(final Path path, final Charset encoding) throws IOException {
        return simplifiedParse(COMPILATION_UNIT, provider(path, encoding)).setStorage(path);
    }

    /**
     * Parses the Java code contained in a file and returns a
     * {@link CompilationUnit} that represents it.<br>
     * Note: Uses UTF-8 encoding
     *
     * @param path path to a file containing Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parse(final Path path) throws IOException {
        return simplifiedParse(COMPILATION_UNIT, provider(path)).setStorage(path);
    }

    /**
     * Parses the Java code contained in a resource and returns a
     * {@link CompilationUnit} that represents it.<br>
     * Note: Uses UTF-8 encoding
     *
     * @param path path to a resource containing Java source code. As resource is accessed through a class loader, a
     * leading "/" is not allowed in pathToResource
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parseResource(final String path) throws IOException {
        return simplifiedParse(COMPILATION_UNIT, resourceProvider(path));
    }

    /**
     * Parses the Java code contained in a resource and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param path path to a resource containing Java source code. As resource is accessed through a class loader, a
     * leading "/" is not allowed in pathToResource
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parseResource(final String path, Charset encoding) throws IOException {
        return simplifiedParse(COMPILATION_UNIT, resourceProvider(path, encoding));
    }

    /**
     * Parses the Java code contained in a resource and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param classLoader the classLoader that is asked to load the resource
     * @param path path to a resource containing Java source code. As resource is accessed through a class loader, a
     * leading "/" is not allowed in pathToResource
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parseResource(final ClassLoader classLoader, final String path, Charset encoding) throws IOException {
        return simplifiedParse(COMPILATION_UNIT, resourceProvider(classLoader, path, encoding));
    }

    /**
     * Parses Java code from a Reader and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param reader the reader containing Java source code. It will be closed after parsing.
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(final Reader reader) {
        return simplifiedParse(COMPILATION_UNIT, provider(reader));
    }

    /**
     * Parses the Java code contained in code and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param code Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(String code) {
        return simplifiedParse(COMPILATION_UNIT, provider(code));
    }

    /**
     * Parses the Java block contained in a {@link String} and returns a
     * {@link BlockStmt} that represents it.
     *
     * @param blockStatement {@link String} containing Java block code
     * @return BlockStmt representing the Java block
     * @throws ParseProblemException if the source code has parser errors
     */
    public static BlockStmt parseBlock(final String blockStatement) {
        return simplifiedParse(BLOCK, provider(blockStatement));
    }

    /**
     * Parses the Java statement contained in a {@link String} and returns a
     * {@link Statement} that represents it.
     *
     * @param statement {@link String} containing Java statement code
     * @return Statement representing the Java statement
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Statement parseStatement(final String statement) {
        return simplifiedParse(STATEMENT, provider(statement));
    }

    private static <T extends Node> T simplifiedParse(ParseStart<T> context, Provider provider) {
        ParseResult<T> result = new JavaParser(staticConfiguration).parse(context, provider);
        if (result.isSuccessful()) {
            return result.getResult().get();
        }
        throw new ParseProblemException(result.getProblems());
    }

    /**
     * Parses the Java import contained in a {@link String} and returns a
     * {@link ImportDeclaration} that represents it.
     *
     * @param importDeclaration {@link String} containing Java import code
     * @return ImportDeclaration representing the Java import declaration
     * @throws ParseProblemException if the source code has parser errors
     */
    public static ImportDeclaration parseImport(final String importDeclaration) {
        return simplifiedParse(IMPORT_DECLARATION, provider(importDeclaration));
    }

    /**
     * Parses the Java expression contained in a {@link String} and returns a
     * {@link Expression} that represents it.
     *
     * @param expression {@link String} containing Java expression
     * @return Expression representing the Java expression
     * @throws ParseProblemException if the source code has parser errors
     */
    @SuppressWarnings("unchecked")
    public static <T extends Expression> T parseExpression(final String expression) {
        return (T) simplifiedParse(EXPRESSION, provider(expression));
    }

    /**
     * Parses the Java annotation contained in a {@link String} and returns a
     * {@link AnnotationExpr} that represents it.
     *
     * @param annotation {@link String} containing Java annotation
     * @return AnnotationExpr representing the Java annotation
     * @throws ParseProblemException if the source code has parser errors
     */
    public static AnnotationExpr parseAnnotation(final String annotation) {
        return simplifiedParse(ANNOTATION, provider(annotation));
    }

    /**
     * Parses the Java annotation body declaration(e.g fields or methods) contained in a
     * {@link String} and returns a {@link BodyDeclaration} that represents it.
     *
     * @param body {@link String} containing Java body declaration
     * @return BodyDeclaration representing the Java annotation
     * @throws ParseProblemException if the source code has parser errors
     */
    public static BodyDeclaration<?> parseAnnotationBodyDeclaration(final String body) {
        return simplifiedParse(ANNOTATION_BODY, provider(body));
    }

    /**
     * Parses a Java class body declaration(e.g fields or methods) and returns a
     * {@link BodyDeclaration} that represents it.
     *
     * @param body the body of a class
     * @return BodyDeclaration representing the Java class body
     * @throws ParseProblemException if the source code has parser errors
     * @deprecated just use parseBodyDeclaration now.
     */
    @Deprecated
    public static BodyDeclaration<?> parseClassBodyDeclaration(String body) {
        return parseBodyDeclaration(body);
    }

    /**
     * Parses a Java interface body declaration(e.g fields or methods) and returns a
     * {@link BodyDeclaration} that represents it.
     *
     * @param body the body of an interface
     * @return BodyDeclaration representing the Java interface body
     * @throws ParseProblemException if the source code has parser errors
     * @deprecated just use parseBodyDeclaration now.
     */
    @Deprecated
    public static BodyDeclaration<?> parseInterfaceBodyDeclaration(String body) {
        return parseBodyDeclaration(body);
    }

    /**
     * Parses a Java class or interface body declaration(e.g fields or methods) and returns a
     * {@link BodyDeclaration} that represents it.
     *
     * @param body the body of a class or interface
     * @return BodyDeclaration representing the Java interface body
     * @throws ParseProblemException if the source code has parser errors
     */
    public static BodyDeclaration<?> parseBodyDeclaration(String body) {
        return simplifiedParse(CLASS_BODY, provider(body));
    }

    /**
     * Parses a Java class or interface type name and returns a {@link ClassOrInterfaceType} that represents it.
     *
     * @param type the type name like a.b.c.X or Y
     * @return ClassOrInterfaceType representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static ClassOrInterfaceType parseClassOrInterfaceType(String type) {
        return simplifiedParse(CLASS_OR_INTERFACE_TYPE, provider(type));
    }

    /**
     * Parses a Java type name and returns a {@link Type} that represents it.
     *
     * @param type the type name like a.b.c.X, Y, or int
     * @return ClassOrInterfaceType representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Type parseType(String type) {
        return simplifiedParse(TYPE, provider(type));
    }

    /**
     * Parses a variable declaration expression and returns a {@link com.github.javaparser.ast.expr.VariableDeclarationExpr}
     * that represents it.
     *
     * @param declaration a variable declaration like <code>int x=2;</code>
     * @return VariableDeclarationExpr representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static VariableDeclarationExpr parseVariableDeclarationExpr(String declaration) {
        return simplifiedParse(VARIABLE_DECLARATION_EXPR, provider(declaration));
    }

    /**
     * Parses the content of a JavadocComment and returns a {@link com.github.javaparser.javadoc.Javadoc} that
     * represents it.
     *
     * @param content a variable declaration like <code>content of my javadoc\n * second line\n * third line</code>
     * @return Javadoc representing the content of the comment
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Javadoc parseJavadoc(String content) {
        return JavadocParser.parse(content);
    }

    /**
     * Parses the this(...) and super(...) statements that may occur at the start of a constructor.
     *
     * @param statement a statement like super("hello");
     * @return the AST for the statement.
     * @throws ParseProblemException if the source code has parser errors
     */
    public static ExplicitConstructorInvocationStmt parseExplicitConstructorInvocationStmt(String statement) {
        return simplifiedParse(EXPLICIT_CONSTRUCTOR_INVOCATION_STMT, provider(statement));
    }

    /**
     * Parses a qualified name (one that can have "."s in it) and returns it as a Name.
     *
     * @param qualifiedName a name like "com.laamella.parameter_source"
     * @return the AST for the name
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Name parseName(String qualifiedName) {
        return simplifiedParse(NAME, provider(qualifiedName));
    }

    /**
     * Parses a simple name (one that can NOT have "."s in it) and returns it as a SimpleName.
     *
     * @param name a name like "parameter_source"
     * @return the AST for the name
     * @throws ParseProblemException if the source code has parser errors
     */
    public static SimpleName parseSimpleName(String name) {
        return simplifiedParse(SIMPLE_NAME, provider(name));
    }

    /**
     * Parses a single parameter (a type and a name) and returns it as a Parameter.
     *
     * @param parameter a parameter like "int[] x"
     * @return the AST for the parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Parameter parseParameter(String parameter) {
        return simplifiedParse(PARAMETER, provider(parameter));
    }


    /**
     * Parses a package declaration and returns it as a PackageDeclaration.
     *
     * @param packageDeclaration a declaration like "package com.microsoft.java;"
     * @return the AST for the parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    public static PackageDeclaration parsePackageDeclaration(String packageDeclaration) {
        return simplifiedParse(PACKAGE_DECLARATION, provider(packageDeclaration));
    }
}
