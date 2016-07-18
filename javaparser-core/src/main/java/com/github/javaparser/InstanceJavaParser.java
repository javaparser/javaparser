/*
 * Copyright (C) 2016 The JavaParser Team.
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
import java.util.List;

/**
 * A thin wrapper around ASTParser with a few convenience methods for parsing CompilationUnits, Blocks, Statements, etc.
 * 
 * @author Sebastian Kuerten
 */
public class InstanceJavaParser {
    private final ASTParser astParser;
    private final Provider provider;

    public InstanceJavaParser(Provider provider) {
        this.provider=provider;
        astParser = new ASTParser(provider);
    }

    public InstanceJavaParser(Reader reader) {
        this(new StreamProvider(reader));
    }

    public InstanceJavaParser(InputStream input) throws IOException {
        this(new StreamProvider(input));
    }

    public InstanceJavaParser(InputStream input, String encoding) throws IOException {
        this(new StreamProvider(input, encoding));
    }

    public InstanceJavaParser(File file) throws IOException {
        this(new FileInputStream(file));
    }

    public InstanceJavaParser(File file, String encoding) throws IOException {
        this(new FileInputStream(file), encoding);
    }
    
    public InstanceJavaParser(String source) {
        this(new StringReader(source));
    }

    /**
     * Return the list of tokens that have been encountered while parsing code
     * using this parser.
     *
     * @return a list of tokens
     */
    public List<Token> getTokens() {
        return astParser.getTokens();
    }

    /**
     * Parses the Java code and returns a {@link CompilationUnit} that
     * represents it.
     *
     * @return CompilationUnit representing the Java source code
     * @throws ParseException
     *             if the source code has parser errors
     */
    public CompilationUnit parse() throws ParseException {
        try {
            return astParser.CompilationUnit();
        } finally {
            closeProvider();
        }
    }

    private void closeProvider() {
        try {
            provider.close();
        } catch (IOException e) {
            // Since we're done parsing and have our result, we don't care about any errors.
        }
    }

    /**
     * Parses the Java block and returns a {@link BlockStmt} that represents it.
     *
     * @return BlockStmt representing the Java block
     * @throws ParseException
     *             if the source code has parser errors
     */
    public BlockStmt parseBlock() throws ParseException {
        try{
            return astParser.Block();
        } finally {
            closeProvider();
        }
    }

    /**
     * Parses the Java block and returns a {@link List} of {@link Statement}s
     * that represents it.
     *
     * @return Statement representing the Java statement
     * @throws ParseException
     *             if the source code has parser errors
     */
    public List<?> parseStatements() throws ParseException {
        try {
            return astParser.Statements();
        } finally {
            closeProvider();
        }
    }

    /**
     * Parses the Java statement and returns a {@link Statement} that represents
     * it.
     *
     * @return Statement representing the Java statement
     * @throws ParseException
     *             if the source code has parser errors
     */
    public Statement parseStatement() throws ParseException {
        try {
            return astParser.Statement();
        } finally {
            closeProvider();
        }
    }

    /**
     * Parses the Java import and returns a {@link ImportDeclaration} that
     * represents it.
     *
     * @return ImportDeclaration representing the Java import declaration
     * @throws ParseException
     *             if the source code has parser errors
     */
    public ImportDeclaration parseImport() throws ParseException {
        try {
            return astParser.ImportDeclaration();
        } finally {
            closeProvider();
        }
    }

    /**
     * Parses the Java expression and returns a {@link Expression} that
     * represents it.
     *
     * @return Expression representing the Java expression
     * @throws ParseException
     *             if the source code has parser errors
     */
    public Expression parseExpression() throws ParseException {
        try {
            return astParser.Expression();
        } finally {
            closeProvider();
        }
    }

    /**
     * Parses the Java annotation and returns a {@link AnnotationExpr} that
     * represents it.
     *
     * @return AnnotationExpr representing the Java annotation
     * @throws ParseException
     *             if the source code has parser errors
     */
    public AnnotationExpr parseAnnotation() throws ParseException {
        try {
            return astParser.Annotation();
        } finally {
            closeProvider();
        }
    }

    /**
     * Parses the Java body declaration(e.g fields or methods) and returns a
     * {@link BodyDeclaration} that represents it.
     *
     * @return BodyDeclaration representing the Java body
     * @throws ParseException
     *             if the source code has parser errors
     */
    public BodyDeclaration parseBodyDeclaration() throws ParseException {
        try {
            return astParser.AnnotationBodyDeclaration();
        } finally {
            closeProvider();
        }
    }

    /**
     * Parses the Java body declaration(e.g fields or methods) and returns a
     * {@link BodyDeclaration} that represents it.
     *
     * @param isInterface
     *            whether the parsed source code is an interface.
     *
     * @return BodyDeclaration representing the Java body
     * @throws ParseException
     *             if the source code has parser errors
     */
    public BodyDeclaration parseClassOrInterfaceBodyDeclaration(
            boolean isInterface) throws ParseException {
        try {
            return astParser.ClassOrInterfaceBodyDeclaration(isInterface);
        } finally {
            closeProvider();
        }
    }
}
