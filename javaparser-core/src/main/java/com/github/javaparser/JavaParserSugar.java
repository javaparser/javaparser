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
import com.github.javaparser.ast.modules.ModuleStmt;
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

import static com.github.javaparser.ParseStart.*;
import static com.github.javaparser.Providers.*;

/**
 * Additional methods for parsing Java source code and creating Abstract Syntax Trees.
 */
public interface JavaParserSugar {

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
    <N extends Node> ParseResult<N> parse(ParseStart<N> start, Provider provider);

    /**
     * Parses the Java code contained in the {@link InputStream} and returns a
     * {@link CompilationUnit} that represents it.
     *
     * @param in {@link InputStream} containing Java source code. It will be closed after parsing.
     * @param encoding encoding of the source code
     * @return CompilationUnit representing the Java source code
     * @throws ParseProblemException if the source code has parser errors
     */
    default CompilationUnit parse(final InputStream in, Charset encoding) {
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
    default CompilationUnit parse(final InputStream in) {
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
    default CompilationUnit parse(final File file, final Charset encoding) throws FileNotFoundException {
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
    default CompilationUnit parse(final File file) throws FileNotFoundException {
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
    default CompilationUnit parse(final Path path, final Charset encoding) throws IOException {
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
    default CompilationUnit parse(final Path path) throws IOException {
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
    default CompilationUnit parseResource(final String path) throws IOException {
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
    default CompilationUnit parseResource(final String path, Charset encoding) throws IOException {
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
    default CompilationUnit parseResource(final ClassLoader classLoader, final String path, Charset encoding) throws IOException {
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
    default CompilationUnit parse(final Reader reader) {
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
    default CompilationUnit parse(String code) {
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
    default BlockStmt parseBlock(final String blockStatement) {
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
    default Statement parseStatement(final String statement) {
        return simplifiedParse(STATEMENT, provider(statement));
    }

    default <T extends Node> T simplifiedParse(ParseStart<T> context, Provider provider) {
        ParseResult<T> result = parse(context, provider);
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
    default ImportDeclaration parseImport(final String importDeclaration) {
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
    default <T extends Expression> T parseExpression(final String expression) {
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
    default AnnotationExpr parseAnnotation(final String annotation) {
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
    default BodyDeclaration<?> parseAnnotationBodyDeclaration(final String body) {
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
    default BodyDeclaration<?> parseClassBodyDeclaration(String body) {
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
    default BodyDeclaration<?> parseInterfaceBodyDeclaration(String body) {
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
    default BodyDeclaration<?> parseBodyDeclaration(String body) {
        return simplifiedParse(CLASS_BODY, provider(body));
    }

    /**
     * Parses a Java class or interface type name and returns a {@link ClassOrInterfaceType} that represents it.
     *
     * @param type the type name like a.b.c.X or Y
     * @return ClassOrInterfaceType representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    default ClassOrInterfaceType parseClassOrInterfaceType(String type) {
        return simplifiedParse(CLASS_OR_INTERFACE_TYPE, provider(type));
    }

    /**
     * Parses a Java type name and returns a {@link Type} that represents it.
     *
     * @param type the type name like a.b.c.X, Y, or int
     * @return ClassOrInterfaceType representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    default Type parseType(String type) {
        return simplifiedParse(TYPE, provider(type));
    }

    /**
     * Parses a variable declaration expression and returns a {@link VariableDeclarationExpr}
     * that represents it.
     *
     * @param declaration a variable declaration like <code>int x=2;</code>
     * @return VariableDeclarationExpr representing the type
     * @throws ParseProblemException if the source code has parser errors
     */
    default VariableDeclarationExpr parseVariableDeclarationExpr(String declaration) {
        return simplifiedParse(VARIABLE_DECLARATION_EXPR, provider(declaration));
    }

    /**
     * Parses the content of a JavadocComment and returns a {@link Javadoc} that
     * represents it.
     *
     * @param content a variable declaration like <code>content of my javadoc\n * second line\n * third line</code>
     * @return Javadoc representing the content of the comment
     * @throws ParseProblemException if the source code has parser errors
     */
    default Javadoc parseJavadoc(String content) {
        return new JavadocParser().parse(content);
    }

    /**
     * Parses the this(...) and super(...) statements that may occur at the start of a constructor.
     *
     * @param statement a statement like super("hello");
     * @return the AST for the statement.
     * @throws ParseProblemException if the source code has parser errors
     */
    default ExplicitConstructorInvocationStmt parseExplicitConstructorInvocationStmt(String statement) {
        return simplifiedParse(EXPLICIT_CONSTRUCTOR_INVOCATION_STMT, provider(statement));
    }

    /**
     * Parses a qualified name (one that can have "."s in it) and returns it as a Name.
     *
     * @param qualifiedName a name like "com.laamella.parameter_source"
     * @return the AST for the name
     * @throws ParseProblemException if the source code has parser errors
     */
    default Name parseName(String qualifiedName) {
        return simplifiedParse(NAME, provider(qualifiedName));
    }

    /**
     * Parses a simple name (one that can NOT have "."s in it) and returns it as a SimpleName.
     *
     * @param name a name like "parameter_source"
     * @return the AST for the name
     * @throws ParseProblemException if the source code has parser errors
     */
    default SimpleName parseSimpleName(String name) {
        return simplifiedParse(SIMPLE_NAME, provider(name));
    }

    /**
     * Parses a single parameter (a type and a name) and returns it as a Parameter.
     *
     * @param parameter a parameter like "int[] x"
     * @return the AST for the parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    default Parameter parseParameter(String parameter) {
        return simplifiedParse(PARAMETER, provider(parameter));
    }

    /**
     * Parses a package declaration and returns it as a PackageDeclaration.
     *
     * @param packageDeclaration a declaration like "package com.microsoft.java;"
     * @return the AST for the parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    default PackageDeclaration parsePackageDeclaration(String packageDeclaration) {
        return simplifiedParse(PACKAGE_DECLARATION, provider(packageDeclaration));
    }

    /**
     * Parses a type declaration and returns it as a TypeDeclaration.
     *
     * @param typeDeclaration a declaration like "class X {}"
     * @return the AST for the type declaration
     * @throws ParseProblemException if the source code has parser errors
     */
    default TypeDeclaration<?> parseTypeDeclaration(String typeDeclaration) {
        return simplifiedParse(TYPE_DECLARATION, provider(typeDeclaration));
    }

    /**
     * Parses a module declaration and returns it as a ModuleDeclaration.
     *
     * @param moduleDeclaration a declaration like "module X {}"
     * @return the AST for the module declaration
     * @throws ParseProblemException if the source code has parser errors
     * @see ModuleDeclaration
     */
    default ModuleDeclaration parseModuleDeclaration(String moduleDeclaration) {
        return simplifiedParse(MODULE_DECLARATION, provider(moduleDeclaration));
    }

    /**
     * Parses a module directive and returns it as a ModuleStmt.
     *
     * @param moduleDirective a directive like "opens C;"
     * @return the AST for the module directive
     * @throws ParseProblemException if the source code has parser errors
     * @see ModuleStmt
     */
    default ModuleStmt parseModuleDirective(String moduleDirective) {
        return simplifiedParse(MODULE_DIRECTIVE, provider(moduleDirective));
    }


    /**
     * Parses a type parameter and returns it as a TypeParameter
     *
     * @param typeParameter a parameter like "T extends Serializable"
     * @return the AST for the type parameter
     * @throws ParseProblemException if the source code has parser errors
     */
    default TypeParameter parseTypeParameter(String typeParameter) {
        return simplifiedParse(TYPE_PARAMETER, provider(typeParameter));
    }

}
