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
import com.github.javaparser.quality.NotNull;
import com.github.javaparser.quality.Preconditions;
import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.Path;

/**
 * A simpler, static API than {@link JavaParser}.
 */
public final class StaticJavaParser {

    // use ThreadLocal to resolve possible concurrency issues.
    private static final ThreadLocal<ParserConfiguration> localConfiguration = ThreadLocal.withInitial(ParserConfiguration::new);

    /**
     * Get the configuration for the parse... methods. Deprecated method.
     *
     * @deprecated use {@link #getParserConfiguration()} instead
     */
    @Deprecated
    public static ParserConfiguration getConfiguration() {
        return getParserConfiguration();
    }

    /**
     * Get the configuration for the parse... methods.
     */
    public static ParserConfiguration getParserConfiguration() {
        return localConfiguration.get();
    }

    /**
     * Set the configuration for the static parse... methods.
     * This is a STATIC field, so modifying it will directly change how all static parse... methods work!
     */
    public static void setConfiguration(@NotNull ParserConfiguration configuration) {
        Preconditions.checkNotNull(configuration, "Parameter configuration can't be null.");
        localConfiguration.set(configuration);
    }

    /**
     * Parses the Java code contained in the {@link InputStream} and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param in {@link InputStream} containing Java source code. It will be closed after parsing.
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @deprecated set the encoding in the {@link ParserConfiguration}
     */
    @Deprecated
    public static CompilationUnit parse(@NotNull final InputStream in, @NotNull Charset encoding) {
        Preconditions.checkNotNull(in, "Parameter in can't be null.");
        Preconditions.checkNotNull(encoding, "Parameter encoding can't be null.");
        return handleResult(newParser().parse(in, encoding));
    }

    /**
     * Parses the Java code contained in the {@link InputStream} and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param in {@link InputStream} containing Java source code. It will be closed after parsing.
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(@NotNull final InputStream in) {
        Preconditions.checkNotNull(in, "Parameter in can't be null.");
        return newParserAdapted().parse(in);
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
     * @deprecated set the encoding in the {@link ParserConfiguration}
     */
    @Deprecated
    public static CompilationUnit parse(@NotNull final File file, @NotNull final Charset encoding) throws FileNotFoundException {
        Preconditions.checkNotNull(file, "Parameter file can't be null.");
        Preconditions.checkNotNull(encoding, "Parameter encoding can't be null.");
        return handleResult(newParser().parse(file, encoding));
    }

    /**
     * Parses the Java code contained in a {@link File} and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param file {@link File} containing Java source code. It will be closed after parsing.
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws FileNotFoundException the file was not found
     */
    public static CompilationUnit parse(@NotNull final File file) throws FileNotFoundException {
        Preconditions.checkNotNull(file, "Parameter file can't be null.");
        return newParserAdapted().parse(file);
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
     * @deprecated set the encoding in the {@link ParserConfiguration}
     */
    @Deprecated
    public static CompilationUnit parse(@NotNull final Path path, @NotNull final Charset encoding) throws IOException {
        Preconditions.checkNotNull(path, "Parameter path can't be null.");
        Preconditions.checkNotNull(encoding, "Parameter encoding can't be null.");
        return handleResult(newParser().parse(path, encoding));
    }

    /**
     * Parses the Java code contained in a file and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param path path to a file containing Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parse(@NotNull final Path path) throws IOException {
        Preconditions.checkNotNull(path, "Parameter path can't be null.");
        return newParserAdapted().parse(path);
    }

    /**
     * Parses the Java code contained in a resource and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param path path to a resource containing Java source code. As resource is accessed through a class loader, a
     * leading "/" is not allowed in pathToResource
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     * @throws IOException the path could not be accessed
     */
    public static CompilationUnit parseResource(@NotNull final String path) throws IOException {
        Preconditions.checkNotNull(path, "Parameter path can't be null.");
        return newParserAdapted().parseResource(path);
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
     * @deprecated set the encoding in the {@link ParserConfiguration}
     */
    @Deprecated
    public static CompilationUnit parseResource(@NotNull final String path, @NotNull Charset encoding) throws IOException {
        Preconditions.checkNotNull(path, "Parameter path can't be null.");
        Preconditions.checkNotNull(encoding, "Parameter encoding can't be null.");
        return handleResult(newParser().parseResource(path, encoding));
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
     * @deprecated set the encoding in the {@link ParserConfiguration}
     */
    @Deprecated
    public static CompilationUnit parseResource(@NotNull final ClassLoader classLoader, @NotNull final String path, @NotNull Charset encoding) throws IOException {
        Preconditions.checkNotNull(classLoader, "Parameter classLoader can't be null.");
        Preconditions.checkNotNull(path, "Parameter path can't be null.");
        Preconditions.checkNotNull(encoding, "Parameter encoding can't be null.");
        return handleResult(newParser().parseResource(classLoader, path, encoding));
    }

    /**
     * Parses Java code from a Reader and returns a
     * {@link CompilationUnit} that represents it.<br>
     *
     * @param reader the reader containing Java source code. It will be closed after parsing.
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(@NotNull final Reader reader) {
        Preconditions.checkNotNull(reader, "Parameter reader can't be null.");
        return newParserAdapted().parse(reader);
    }

    /**
     * Parses the Java code contained in code and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param code Java source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    public static CompilationUnit parse(@NotNull String code) {
        Preconditions.checkNotNull(code, "Parameter code can't be null.");
        return newParserAdapted().parse(code);
    }

    /**
     * Parses the Java block contained in a {@link String} and returns a
     * {@link BlockStmt} that represents it.
     *
     * @param blockStatement {@link String} containing Java block code
     * @return BlockStmt representing the Java block
     * @throws ParseProblemException if the source code has parser errors
     */
    public static BlockStmt parseBlock(@NotNull final String blockStatement) {
        Preconditions.checkNotNull(blockStatement, "Parameter blockStatement can't be null.");
        return newParserAdapted().parseBlock(blockStatement);
    }

    /**
     * Parses the Java statement contained in a {@link String} and returns a
     * {@link Statement} that represents it.
     *
     * @param statement {@link String} containing Java statement code
     * @return Statement representing the Java statement
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Statement parseStatement(@NotNull final String statement) {
        Preconditions.checkNotNull(statement, "Parameter statement can't be null.");
        return newParserAdapted().parseStatement(statement);
    }

    /**
     * Parses the Java import contained in a {@link String} and returns a
     * {@link ImportDeclaration} that represents it.
     *
     * @param importDeclaration {@link String} containing Java import code
     * @return ImportDeclaration representing the Java import declaration
     * @throws ParseProblemException if the source code has parser errors
     */
    public static ImportDeclaration parseImport(@NotNull final String importDeclaration) {
        Preconditions.checkNotNull(importDeclaration, "Parameter importDeclaration can't be null.");
        return newParserAdapted().parseImport(importDeclaration);
    }

    /**
     * Parses the Java expression contained in a {@link String} and returns a
     * {@link Expression} that represents it.
     *
     * @param expression {@link String} containing Java expression
     * @return Expression representing the Java expression
     * @throws ParseProblemException if the source code has parser errors
     */
    public static <T extends Expression> T parseExpression(@NotNull final String expression) {
        Preconditions.checkNotNull(expression, "Parameter expression can't be null.");
        return newParserAdapted().parseExpression(expression);
    }

    /**
     * Parses the Java annotation contained in a {@link String} and returns a
     * {@link AnnotationExpr} that represents it.
     *
     * @param annotation {@link String} containing Java annotation
     * @return AnnotationExpr representing the Java annotation
     * @throws ParseProblemException if the source code has parser errors
     */
    public static AnnotationExpr parseAnnotation(@NotNull final String annotation) {
        Preconditions.checkNotNull(annotation, "Parameter annotation can't be null.");
        return newParserAdapted().parseAnnotation(annotation);
    }

    /**
     * Parses the Java annotation body declaration(e.g fields or methods) contained in a
     * {@link String} and returns a {@link BodyDeclaration} that represents it.
     *
     * @param body {@link String} containing Java body declaration
     * @return BodyDeclaration representing the Java annotation
     * @throws ParseProblemException if the source code has parser errors
     */
    public static BodyDeclaration<?> parseAnnotationBodyDeclaration(@NotNull final String body) {
        Preconditions.checkNotNull(body, "Parameter body can't be null.");
        return newParserAdapted().parseAnnotationBodyDeclaration(body);
    }

    /**
     * Parses a Java class or interface body declaration(e.g fields or methods) and returns a
     * {@link BodyDeclaration} that represents it.
     *
     * @param body the body of a class or interface
     * @return BodyDeclaration representing the Java interface body
     * @throws ParseProblemException if the source code has parser errors
     */
    public static BodyDeclaration<?> parseBodyDeclaration(@NotNull String body) {
        Preconditions.checkNotNull(body, "Parameter body can't be null.");
        return newParserAdapted().parseBodyDeclaration(body);
    }

    /**
     * Parses a Java class or interface type name and returns a {@link ClassOrInterfaceType} that represents it.
     *
     * @param type the type name like a.b.c.X or Y
     * @return ClassOrInterfaceType representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static ClassOrInterfaceType parseClassOrInterfaceType(@NotNull String type) {
        Preconditions.checkNotNull(type, "Parameter type can't be null.");
        return newParserAdapted().parseClassOrInterfaceType(type);
    }

    /**
     * Parses a Java type name and returns a {@link Type} that represents it.
     *
     * @param type the type name like a.b.c.X, Y, or int
     * @return ClassOrInterfaceType representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Type parseType(@NotNull String type) {
        Preconditions.checkNotNull(type, "Parameter type can't be null.");
        return newParserAdapted().parseType(type);
    }

    /**
     * Parses a variable declaration expression and returns a {@link VariableDeclarationExpr}
     * that represents it.
     *
     * @param declaration a variable declaration like {@code int x=2;}
     * @return VariableDeclarationExpr representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static VariableDeclarationExpr parseVariableDeclarationExpr(@NotNull String declaration) {
        Preconditions.checkNotNull(declaration, "Parameter declaration can't be null.");
        return newParserAdapted().parseVariableDeclarationExpr(declaration);
    }

    /**
     * Parses the content of a JavadocComment and returns a {@link Javadoc} that
     * represents it.
     *
     * @param content a variable declaration like {@code content of my javadoc\n * second line\n * third line}
     * @return Javadoc representing the content of the comment
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Javadoc parseJavadoc(@NotNull String content) {
        Preconditions.checkNotNull(content, "Parameter content can't be null.");
        return JavadocParser.parse(content);
    }

    /**
     * Parses the this(...) and super(...) statements that may occur at the start of a constructor.
     *
     * @param statement a statement like super("hello");
     * @return the AST for the statement.
     * @throws ParseProblemException if the source code has parser errors
     */
    public static ExplicitConstructorInvocationStmt parseExplicitConstructorInvocationStmt(@NotNull String statement) {
        Preconditions.checkNotNull(statement, "Parameter statement can't be null.");
        return newParserAdapted().parseExplicitConstructorInvocationStmt(statement);
    }

    /**
     * Parses a qualified name (one that can have "."s in it) and returns it as a Name.
     *
     * @param qualifiedName a name like "com.laamella.parameter_source"
     * @return the AST for the name
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Name parseName(@NotNull String qualifiedName) {
        Preconditions.checkNotNull(qualifiedName, "Parameter qualifiedName can't be null.");
        return newParserAdapted().parseName(qualifiedName);
    }

    /**
     * Parses a simple name (one that can NOT have "."s in it) and returns it as a SimpleName.
     *
     * @param name a name like "parameter_source"
     * @return the AST for the name
     * @throws ParseProblemException if the source code has parser errors
     */
    public static SimpleName parseSimpleName(@NotNull String name) {
        Preconditions.checkNotNull(name, "Parameter name can't be null.");
        return newParserAdapted().parseSimpleName(name);
    }

    /**
     * Parses a single parameter (a type and a name) and returns it as a Parameter.
     *
     * @param parameter a parameter like "int[] x"
     * @return the AST for the parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Parameter parseParameter(@NotNull String parameter) {
        Preconditions.checkNotNull(parameter, "Parameter parameter can't be null.");
        return newParserAdapted().parseParameter(parameter);
    }

    /**
     * Parses a package declaration and returns it as a PackageDeclaration.
     *
     * @param packageDeclaration a declaration like "package com.microsoft.java;"
     * @return the AST for the parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    public static PackageDeclaration parsePackageDeclaration(@NotNull String packageDeclaration) {
        Preconditions.checkNotNull(packageDeclaration, "Parameter packageDeclaration can't be null.");
        return newParserAdapted().parsePackageDeclaration(packageDeclaration);
    }

    /**
     * Parses a type declaration and returns it as a TypeDeclaration.
     *
     * @param typeDeclaration a declaration like "class X {}"
     * @return the AST for the type declaration
     * @throws ParseProblemException if the source code has parser errors
     */
    public static TypeDeclaration<?> parseTypeDeclaration(@NotNull String typeDeclaration) {
        Preconditions.checkNotNull(typeDeclaration, "Parameter typeDeclaration can't be null.");
        return newParserAdapted().parseTypeDeclaration(typeDeclaration);
    }

    /**
     * Parses a module declaration and returns it as a ModuleDeclaration.
     *
     * @param moduleDeclaration a declaration like "module X {}"
     * @return the AST for the module declaration
     * @throws ParseProblemException if the source code has parser errors
     * @see ModuleDeclaration
     */
    public static ModuleDeclaration parseModuleDeclaration(@NotNull String moduleDeclaration) {
        Preconditions.checkNotNull(moduleDeclaration, "Parameter moduleDeclaration can't be null.");
        return newParserAdapted().parseModuleDeclaration(moduleDeclaration);
    }

    /**
     * Parses a module directive and returns it as a ModuleDirective.
     *
     * @param moduleDirective a directive like "opens C;"
     * @return the AST for the module directive
     * @throws ParseProblemException if the source code has parser errors
     * @see ModuleDirective
     */
    public static ModuleDirective parseModuleDirective(@NotNull String moduleDirective) {
        Preconditions.checkNotNull(moduleDirective, "Parameter moduleDirective can't be null.");
        return newParserAdapted().parseModuleDirective(moduleDirective);
    }

    /**
     * Parses a type parameter and returns it as a TypeParameter
     *
     * @param typeParameter a parameter like "T extends Serializable"
     * @return the AST for the type parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    public static TypeParameter parseTypeParameter(@NotNull String typeParameter) {
        Preconditions.checkNotNull(typeParameter, "Parameter typeParameter can't be null.");
        return newParserAdapted().parseTypeParameter(typeParameter);
    }

    /**
     * Parses a method declaration and returns it as a MethodDeclaration.
     *
     * @param methodDeclaration a method declaration like "void foo() {}"
     * @return the AST for the method declaration
     * @throws ParseProblemException if the source code has parser errors
     * @see MethodDeclaration
     */
    public static MethodDeclaration parseMethodDeclaration(@NotNull String methodDeclaration) {
        Preconditions.checkNotNull(methodDeclaration, "Parameter methodDeclaration can't be null.");
        return newParserAdapted().parseMethodDeclaration(methodDeclaration);
    }

    // Private methods
    private static JavaParser newParser() {
        return new JavaParser(getParserConfiguration());
    }

    private static JavaParserAdapter newParserAdapted() {
        return new JavaParserAdapter(newParser());
    }

    @Deprecated
    private static <T extends Node> T handleResult(ParseResult<T> result) {
        if (result.isSuccessful()) {
            return result.getResult().get();
        }
        throw new ParseProblemException(result.getProblems());
    }

    private StaticJavaParser() {
    }
}
