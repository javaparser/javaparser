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

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.PackageDeclaration;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.modules.ModuleDeclaration;
import com.github.javaparser.ast.modules.ModuleDirective;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.TypeParameter;
import com.github.javaparser.javadoc.Javadoc;

import java.io.*;
import java.nio.file.Path;
import java.util.Optional;

/**
 * A simpler API for {@link JavaParser}.
 */
public final class SimpleJavaParser {

	private final JavaParser parser;

    /**
     * Create a new instance of {@link SimpleJavaParser} with the default configuration.
     */
	public SimpleJavaParser() {
        this( new JavaParser() );
	}

    /**
     * Create a new instance of {@link SimpleJavaParser} with a custom configuration.
     *
     * @param configuration The configuration to be used in the parser.
     */
	public SimpleJavaParser(ParserConfiguration configuration) {
        this( new JavaParser(configuration) );
	}

	/**
	 * Create a new instance of {@link SimpleJavaParser} with the provided {@link JavaParser}.
	 * <br>
	 * This constructor is used for testing purposes.
	 *
	 * @param parser The parser to be used.
	 */
	SimpleJavaParser(JavaParser parser) {
		this.parser = parser;
	}

	/**
	 * Get the instance of {@link JavaParser} being wrapped.
	 *
	 * @return The wrapped parser.
	 */
	public JavaParser getWrappedParser() {
		return parser;
	}

	/**
     * Helper function to handle the results in a simpler way.
     *
     * @param result The result to be processed.
     *
     * @param <T> The expected return type.
     *
     * @return The parsed value.
     */
	private <T extends Node> T handleResult(ParseResult<T> result) {
	    if (result.isSuccessful()) {

            Optional<T> results = result.getResult();
            if (results.isPresent())
                return results.get();
            else
                throw new IllegalStateException("Parsed results is marked as successful but no result present.");
        } else
            throw new ParseProblemException(result.getProblems());
	}

	/**
	 * Parses the Java code contained in the {@link InputStream} and returns a
	 * {@link CompilationUnit} that represents it.<br>
	 *
	 * @param in {@link InputStream} containing Java source code. It will be closed after parsing.
	 *
	 * @return CompilationUnit representing the Java source code
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public CompilationUnit parse(final InputStream in) {
		return handleResult(getWrappedParser().parse(in));
	}

	/**
	 * Parses the Java code contained in a {@link File} and returns a
	 * {@link CompilationUnit} that represents it.<br>
	 *
	 * @param file {@link File} containing Java source code. It will be closed after parsing.
	 *
	 * @return CompilationUnit representing the Java source code
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 * @throws FileNotFoundException the file was not found
	 */
	public CompilationUnit parse(final File file) throws FileNotFoundException {
		return handleResult(getWrappedParser().parse(file));
	}

	/**
	 * Parses the Java code contained in a file and returns a
	 * {@link CompilationUnit} that represents it.<br>
	 *
	 * @param path path to a file containing Java source code
	 *
	 * @return CompilationUnit representing the Java source code
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 * @throws IOException           the path could not be accessed
	 */
	public CompilationUnit parse(final Path path) throws IOException {
		return handleResult(getWrappedParser().parse(path));
	}

	/**
	 * Parses the Java code contained in a resource and returns a
	 * {@link CompilationUnit} that represents it.<br>
	 *
	 * @param path path to a resource containing Java source code. As resource is accessed through a class loader, a
	 *             leading "/" is not allowed in pathToResource
	 *
	 * @return CompilationUnit representing the Java source code
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 * @throws IOException           the path could not be accessed
	 */
	public CompilationUnit parseResource(final String path) throws IOException {
		return handleResult(getWrappedParser().parseResource(path));
	}

	/**
	 * Parses Java code from a Reader and returns a
	 * {@link CompilationUnit} that represents it.<br>
	 *
	 * @param reader the reader containing Java source code. It will be closed after parsing.
	 *
	 * @return CompilationUnit representing the Java source code
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public CompilationUnit parse(final Reader reader) {
		return handleResult(getWrappedParser().parse(reader));
	}

	/**
	 * Parses the Java code contained in code and returns a
	 * {@link CompilationUnit} that represents it.
	 *
	 * @param code Java source code
	 *
	 * @return CompilationUnit representing the Java source code
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public CompilationUnit parse(String code) {
		return handleResult(getWrappedParser().parse(code));
	}

	/**
	 * Parses the Java block contained in a {@link String} and returns a
	 * {@link BlockStmt} that represents it.
	 *
	 * @param blockStatement {@link String} containing Java block code
	 *
	 * @return BlockStmt representing the Java block
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public BlockStmt parseBlock(final String blockStatement) {
		return handleResult(getWrappedParser().parseBlock(blockStatement));
	}

	/**
	 * Parses the Java statement contained in a {@link String} and returns a
	 * {@link Statement} that represents it.
	 *
	 * @param statement {@link String} containing Java statement code
	 *
	 * @return Statement representing the Java statement
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public Statement parseStatement(final String statement) {
		return handleResult(getWrappedParser().parseStatement(statement));
	}

	/**
	 * Parses the Java import contained in a {@link String} and returns a
	 * {@link ImportDeclaration} that represents it.
	 *
	 * @param importDeclaration {@link String} containing Java import code
	 *
	 * @return ImportDeclaration representing the Java import declaration
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public ImportDeclaration parseImport(final String importDeclaration) {
		return handleResult(getWrappedParser().parseImport(importDeclaration));
	}

	/**
	 * Parses the Java expression contained in a {@link String} and returns a
	 * {@link Expression} that represents it.
	 *
	 * @param expression {@link String} containing Java expression
	 *
	 * @return Expression representing the Java expression
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public <T extends Expression> T parseExpression(final String expression) {
		return handleResult(getWrappedParser().parseExpression(expression));
	}

	/**
	 * Parses the Java annotation contained in a {@link String} and returns a
	 * {@link AnnotationExpr} that represents it.
	 *
	 * @param annotation {@link String} containing Java annotation
	 *
	 * @return AnnotationExpr representing the Java annotation
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public AnnotationExpr parseAnnotation(final String annotation) {
		return handleResult(getWrappedParser().parseAnnotation(annotation));
	}

	/**
	 * Parses the Java annotation body declaration(e.g fields or methods) contained in a
	 * {@link String} and returns a {@link BodyDeclaration} that represents it.
	 *
	 * @param body {@link String} containing Java body declaration
	 *
	 * @return BodyDeclaration representing the Java annotation
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public BodyDeclaration<?> parseAnnotationBodyDeclaration(final String body) {
		return handleResult(getWrappedParser().parseAnnotationBodyDeclaration(body));
	}

	/**
	 * Parses a Java class or interface body declaration(e.g fields or methods) and returns a
	 * {@link BodyDeclaration} that represents it.
	 *
	 * @param body the body of a class or interface
	 *
	 * @return BodyDeclaration representing the Java interface body
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public BodyDeclaration<?> parseBodyDeclaration(String body) {
		return handleResult(getWrappedParser().parseBodyDeclaration(body));
	}

	/**
	 * Parses a Java class or interface type name and returns a {@link ClassOrInterfaceType} that represents it.
	 *
	 * @param type the type name like a.b.c.X or Y
	 *
	 * @return ClassOrInterfaceType representing the type
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public ClassOrInterfaceType parseClassOrInterfaceType(String type) {
		return handleResult(getWrappedParser().parseClassOrInterfaceType(type));
	}

	/**
	 * Parses a Java type name and returns a {@link Type} that represents it.
	 *
	 * @param type the type name like a.b.c.X, Y, or int
	 *
	 * @return ClassOrInterfaceType representing the type
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public Type parseType(String type) {
		return handleResult(getWrappedParser().parseType(type));
	}

	/**
	 * Parses a variable declaration expression and returns a {@link VariableDeclarationExpr}
	 * that represents it.
	 *
	 * @param declaration a variable declaration like {@code int x=2;}
	 *
	 * @return VariableDeclarationExpr representing the type
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public VariableDeclarationExpr parseVariableDeclarationExpr(String declaration) {
		return handleResult(getWrappedParser().parseVariableDeclarationExpr(declaration));
	}

	/**
	 * Parses the content of a JavadocComment and returns a {@link Javadoc} that
	 * represents it.
	 *
	 * @param content a variable declaration like {@code content of my javadoc\n * second line\n * third line}
	 *
	 * @return Javadoc representing the content of the comment
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public Javadoc parseJavadoc(String content) {
		return JavadocParser.parse(content);
	}

	/**
	 * Parses the this(...) and super(...) statements that may occur at the start of a constructor.
	 *
	 * @param statement a statement like super("hello");
	 *
	 * @return the AST for the statement.
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public ExplicitConstructorInvocationStmt parseExplicitConstructorInvocationStmt(String statement) {
		return handleResult(getWrappedParser().parseExplicitConstructorInvocationStmt(statement));
	}

	/**
	 * Parses a qualified name (one that can have "."s in it) and returns it as a Name.
	 *
	 * @param qualifiedName a name like "com.laamella.parameter_source"
	 *
	 * @return the AST for the name
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public Name parseName(String qualifiedName) {
		return handleResult(getWrappedParser().parseName(qualifiedName));
	}

	/**
	 * Parses a simple name (one that can NOT have "."s in it) and returns it as a SimpleName.
	 *
	 * @param name a name like "parameter_source"
	 *
	 * @return the AST for the name
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public SimpleName parseSimpleName(String name) {
		return handleResult(getWrappedParser().parseSimpleName(name));
	}

	/**
	 * Parses a single parameter (a type and a name) and returns it as a Parameter.
	 *
	 * @param parameter a parameter like "int[] x"
	 *
	 * @return the AST for the parameter
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public Parameter parseParameter(String parameter) {
		return handleResult(getWrappedParser().parseParameter(parameter));
	}

	/**
	 * Parses a package declaration and returns it as a PackageDeclaration.
	 *
	 * @param packageDeclaration a declaration like "package com.microsoft.java;"
	 *
	 * @return the AST for the parameter
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public PackageDeclaration parsePackageDeclaration(String packageDeclaration) {
		return handleResult(getWrappedParser().parsePackageDeclaration(packageDeclaration));
	}

	/**
	 * Parses a type declaration and returns it as a TypeDeclaration.
	 *
	 * @param typeDeclaration a declaration like "class X {}"
	 *
	 * @return the AST for the type declaration
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public TypeDeclaration<?> parseTypeDeclaration(String typeDeclaration) {
		return handleResult(getWrappedParser().parseTypeDeclaration(typeDeclaration));
	}

	/**
	 * Parses a module declaration and returns it as a ModuleDeclaration.
	 *
	 * @param moduleDeclaration a declaration like "module X {}"
	 *
	 * @return the AST for the module declaration
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 * @see ModuleDeclaration
	 */
	public ModuleDeclaration parseModuleDeclaration(String moduleDeclaration) {
		return handleResult(getWrappedParser().parseModuleDeclaration(moduleDeclaration));
	}

	/**
	 * Parses a module directive and returns it as a ModuleDirective.
	 *
	 * @param moduleDirective a directive like "opens C;"
	 *
	 * @return the AST for the module directive
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 * @see ModuleDirective
	 */
	public ModuleDirective parseModuleDirective(String moduleDirective) {
		return handleResult(getWrappedParser().parseModuleDirective(moduleDirective));
	}

	/**
	 * Parses a type parameter and returns it as a TypeParameter
	 *
	 * @param typeParameter a parameter like "T extends Serializable"
	 *
	 * @return the AST for the type parameter
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 */
	public TypeParameter parseTypeParameter(String typeParameter) {
		return handleResult(getWrappedParser().parseTypeParameter(typeParameter));
	}

	/**
	 * Parses a method declaration and returns it as a MethodDeclaration.
	 *
	 * @param methodDeclaration a method declaration like "void foo() {}"
	 *
	 * @return the AST for the method declaration
	 *
	 * @throws ParseProblemException if the source code has parser errors
	 * @see MethodDeclaration
	 */
	public MethodDeclaration parseMethodDeclaration(String methodDeclaration) {
		return handleResult(getWrappedParser().parseMethodDeclaration(methodDeclaration));
	}

}
