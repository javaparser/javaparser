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
import java.nio.charset.Charset;
import java.nio.file.Path;

/**
 * A simpler, static API than {@link JavaParser}.
 */
public final class StaticJavaParser {
    private static ParserConfiguration configuration = new ParserConfiguration();

    private StaticJavaParser() {
    }

    /**
     * Get the configuration for the parse... methods.
     */
    public static ParserConfiguration getConfiguration() {
        return configuration;
    }

    /**
     * Set the configuration for the static parse... methods.
     * This is a STATIC field, so modifying it will directly change how all static parse... methods work!
     */
    public static void setConfiguration(ParserConfiguration configuration) {
        StaticJavaParser.configuration = configuration;
    }

    private static JavaParser newParser() {
        return new JavaParser(configuration);
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
    public static CompilationUnit parse(final InputStream in, Charset encoding) {
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
    public static CompilationUnit parse(final InputStream in) {
        return handleResult(newParser().parse(in));
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
    public static CompilationUnit parse(final File file, final Charset encoding) throws FileNotFoundException {
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
    public static CompilationUnit parse(final File file) throws FileNotFoundException {
        return handleResult(newParser().parse(file));
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
    public static CompilationUnit parse(final Path path, final Charset encoding) throws IOException {
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
    public static CompilationUnit parse(final Path path) throws IOException {
        return handleResult(newParser().parse(path));
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
    public static CompilationUnit parseResource(final String path) throws IOException {
        return handleResult(newParser().parseResource(path));
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
    public static CompilationUnit parseResource(final String path, Charset encoding) throws IOException {
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
    public static CompilationUnit parseResource(final ClassLoader classLoader, final String path, Charset encoding) throws IOException {
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
    public static CompilationUnit parse(final Reader reader) {
        return handleResult(newParser().parse(reader));
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
        return handleResult(newParser().parse(code));
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
        return handleResult(newParser().parseBlock(blockStatement));
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
        return handleResult(newParser().parseStatement(statement));
    }

    private static <T extends Node> T handleResult(ParseResult<T> result) {
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
        return handleResult(newParser().parseImport(importDeclaration));
    }

    /**
     * Parses the Java expression contained in a {@link String} and returns a
     * {@link Expression} that represents it.
     *
     * @param expression {@link String} containing Java expression
     * @return Expression representing the Java expression
     * @throws ParseProblemException if the source code has parser errors
     */
    public static <T extends Expression> T parseExpression(final String expression) {
        return handleResult(newParser().parseExpression(expression));
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
        return handleResult(newParser().parseAnnotation(annotation));
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
        return handleResult(newParser().parseAnnotationBodyDeclaration(body));
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
        return handleResult(newParser().parseBodyDeclaration(body));
    }

    /**
     * Parses a Java class or interface type name and returns a {@link ClassOrInterfaceType} that represents it.
     *
     * @param type the type name like a.b.c.X or Y
     * @return ClassOrInterfaceType representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static ClassOrInterfaceType parseClassOrInterfaceType(String type) {
        return handleResult(newParser().parseClassOrInterfaceType(type));
    }

    /**
     * Parses a Java type name and returns a {@link Type} that represents it.
     *
     * @param type the type name like a.b.c.X, Y, or int
     * @return ClassOrInterfaceType representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Type parseType(String type) {
        return handleResult(newParser().parseType(type));
    }

    /**
     * Parses a variable declaration expression and returns a {@link VariableDeclarationExpr}
     * that represents it.
     *
     * @param declaration a variable declaration like <code>int x=2;</code>
     * @return VariableDeclarationExpr representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    public static VariableDeclarationExpr parseVariableDeclarationExpr(String declaration) {
        return handleResult(newParser().parseVariableDeclarationExpr(declaration));
    }

    /**
     * Parses the content of a JavadocComment and returns a {@link Javadoc} that
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
        return handleResult(newParser().parseExplicitConstructorInvocationStmt(statement));
    }

    /**
     * Parses a qualified name (one that can have "."s in it) and returns it as a Name.
     *
     * @param qualifiedName a name like "com.laamella.parameter_source"
     * @return the AST for the name
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Name parseName(String qualifiedName) {
        return handleResult(newParser().parseName(qualifiedName));
    }

    /**
     * Parses a simple name (one that can NOT have "."s in it) and returns it as a SimpleName.
     *
     * @param name a name like "parameter_source"
     * @return the AST for the name
     * @throws ParseProblemException if the source code has parser errors
     */
    public static SimpleName parseSimpleName(String name) {
        return handleResult(newParser().parseSimpleName(name));
    }

    /**
     * Parses a single parameter (a type and a name) and returns it as a Parameter.
     *
     * @param parameter a parameter like "int[] x"
     * @return the AST for the parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    public static Parameter parseParameter(String parameter) {
        return handleResult(newParser().parseParameter(parameter));
    }

    /**
     * Parses a package declaration and returns it as a PackageDeclaration.
     *
     * @param packageDeclaration a declaration like "package com.microsoft.java;"
     * @return the AST for the parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    public static PackageDeclaration parsePackageDeclaration(String packageDeclaration) {
        return handleResult(newParser().parsePackageDeclaration(packageDeclaration));
    }

    /**
     * Parses a type declaration and returns it as a TypeDeclaration.
     *
     * @param typeDeclaration a declaration like "class X {}"
     * @return the AST for the type declaration
     * @throws ParseProblemException if the source code has parser errors
     */
    public static TypeDeclaration<?> parseTypeDeclaration(String typeDeclaration) {
        return handleResult(newParser().parseTypeDeclaration(typeDeclaration));
    }

    /**
     * Parses a module declaration and returns it as a ModuleDeclaration.
     *
     * @param moduleDeclaration a declaration like "module X {}"
     * @return the AST for the module declaration
     * @throws ParseProblemException if the source code has parser errors
     * @see ModuleDeclaration
     */
    public static ModuleDeclaration parseModuleDeclaration(String moduleDeclaration) {
        return handleResult(newParser().parseModuleDeclaration(moduleDeclaration));
    }

    /**
     * Parses a module directive and returns it as a ModuleDirective.
     *
     * @param moduleDirective a directive like "opens C;"
     * @return the AST for the module directive
     * @throws ParseProblemException if the source code has parser errors
     * @see ModuleDirective
     */
    public static ModuleDirective parseModuleDirective(String moduleDirective) {
        return handleResult(newParser().parseModuleDirective(moduleDirective));
    }


    /**
     * Parses a type parameter and returns it as a TypeParameter
     *
     * @param typeParameter a parameter like "T extends Serializable"
     * @return the AST for the type parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    public static TypeParameter parseTypeParameter(String typeParameter) {
        return handleResult(newParser().parseTypeParameter(typeParameter));
    }

}
