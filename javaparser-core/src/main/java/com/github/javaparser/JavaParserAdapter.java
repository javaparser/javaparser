/*
 * Copyright (C) 2013-2023 The JavaParser Team.
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
import java.util.Objects;

public class JavaParserAdapter {

    /**
     * Wraps the {@link JavaParser}.
     *
     * @param parser The java parser to be used.
     *
     * @return The created QuickJavaParser.
     */
    public static JavaParserAdapter of(JavaParser parser) {
        return new JavaParserAdapter(parser);
    }

    private final JavaParser parser;

    public JavaParserAdapter(JavaParser parser) {
        this.parser = Objects.requireNonNull(parser, "A non-null parser should be provided.");
    }

    public JavaParser getParser() {
        return parser;
    }

    /**
     * Helper function to handle the result in a simpler way.
     *
     * @param result The result to be handled.
     *
     * @param <T> The return type.
     *
     * @return The parsed value.
     */
    private <T extends Node> T handleResult(ParseResult<T> result) {
        if (result.isSuccessful()) {
            return result.getResult().orElse(null);
        }
        throw new ParseProblemException(result.getProblems());
    }

    public ParserConfiguration getParserConfiguration() {
        return parser.getParserConfiguration();
    }

    public CompilationUnit parse(InputStream in) {
        return handleResult(getParser().parse(in));
    }

    public CompilationUnit parse(File file) throws FileNotFoundException {
        return handleResult(getParser().parse(file));
    }

    public CompilationUnit parse(Path path) throws IOException {
        return handleResult(getParser().parse(path));
    }

    public CompilationUnit parse(Reader reader) {
        return handleResult(getParser().parse(reader));
    }

    public CompilationUnit parse(String code) {
        return handleResult(getParser().parse(code));
    }

    public CompilationUnit parseResource(String path) throws IOException {
        return handleResult(getParser().parseResource(path));
    }

    public BlockStmt parseBlock(String blockStatement) {
        return handleResult(getParser().parseBlock(blockStatement));
    }

    public Statement parseStatement(String statement) {
        return handleResult(getParser().parseStatement(statement));
    }

    public ImportDeclaration parseImport(String importDeclaration) {
        return handleResult(getParser().parseImport(importDeclaration));
    }

    public <T extends Expression> T parseExpression(String expression) {
        return handleResult(getParser().parseExpression(expression));
    }

    public AnnotationExpr parseAnnotation(String annotation) {
        return handleResult(getParser().parseAnnotation(annotation));
    }

    public BodyDeclaration<?> parseAnnotationBodyDeclaration(String body) {
        return handleResult(getParser().parseAnnotationBodyDeclaration(body));
    }

    public BodyDeclaration<?> parseBodyDeclaration(String body) {
        return handleResult(getParser().parseBodyDeclaration(body));
    }

    public ClassOrInterfaceType parseClassOrInterfaceType(String type) {
        return handleResult(getParser().parseClassOrInterfaceType(type));
    }

    public Type parseType(String type) {
        return handleResult(getParser().parseType(type));
    }

    public VariableDeclarationExpr parseVariableDeclarationExpr(String declaration) {
        return handleResult(getParser().parseVariableDeclarationExpr(declaration));
    }

    public Javadoc parseJavadoc(String content) {
        return JavadocParser.parse(content);
    }

    public ExplicitConstructorInvocationStmt parseExplicitConstructorInvocationStmt(String statement) {
        return handleResult(getParser().parseExplicitConstructorInvocationStmt(statement));
    }

    public Name parseName(String qualifiedName) {
        return handleResult(getParser().parseName(qualifiedName));
    }

    public SimpleName parseSimpleName(String name) {
        return handleResult(getParser().parseSimpleName(name));
    }

    public Parameter parseParameter(String parameter) {
        return handleResult(getParser().parseParameter(parameter));
    }

    public PackageDeclaration parsePackageDeclaration(String packageDeclaration) {
        return handleResult(getParser().parsePackageDeclaration(packageDeclaration));
    }

    public TypeDeclaration<?> parseTypeDeclaration(String typeDeclaration) {
        return handleResult(getParser().parseTypeDeclaration(typeDeclaration));
    }

    public ModuleDeclaration parseModuleDeclaration(String moduleDeclaration) {
        return handleResult(getParser().parseModuleDeclaration(moduleDeclaration));
    }

    public ModuleDirective parseModuleDirective(String moduleDirective) {
        return handleResult(getParser().parseModuleDirective(moduleDirective));
    }

    public TypeParameter parseTypeParameter(String typeParameter) {
        return handleResult(getParser().parseTypeParameter(typeParameter));
    }

    public MethodDeclaration parseMethodDeclaration(String methodDeclaration) {
        return handleResult(getParser().parseMethodDeclaration(methodDeclaration));
    }
}
