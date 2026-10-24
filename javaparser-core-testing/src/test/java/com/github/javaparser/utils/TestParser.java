/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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

package com.github.javaparser.utils;

import static com.github.javaparser.ParserConfiguration.LanguageLevel;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.jupiter.api.Assertions.fail;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.Statement;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Supplier;

public class TestParser {

    /*
     * Parsers are cached per language level and shared statically across all tests. This is safe only because tests
     * run sequentially (JUnit's default lifecycle) and the cached parsers' configuration is never mutated after
     * creation.
     *
     * WARNING: JavaParser is not thread-safe. If parallel test execution is ever enabled, these shared instances
     * become a data race. The cache would then have to be made thread-local (one parser per level per thread) or
     * dropped (create a fresh parser per call).
     */
    private static final Map<LanguageLevel, JavaParserAdapter> parserCache = new HashMap<>();

    private static JavaParserAdapter parser(LanguageLevel languageLevel) {
        return parserCache.computeIfAbsent(
                languageLevel, ll -> StaticJavaParser.newParserAdapter(new ParserConfiguration().setLanguageLevel(ll)));
    }

    private static <T> T parse(Supplier<T> operation) {
        try {
            return operation.get();
        } catch (ParseProblemException e) {
            return fail(e.getProblems().toString());
        }
    }

    public static CompilationUnit parseCompilationUnit(String stmt) {
        return parse(() -> parser(BLEEDING_EDGE).parse(stmt));
    }

    public static Statement parseStatement(String stmt) {
        return parse(() -> parser(BLEEDING_EDGE).parseStatement(stmt));
    }

    public static <T extends Expression> T parseExpression(String expr) {
        return parse(() -> parser(BLEEDING_EDGE).parseExpression(expr));
    }

    public static <T extends BodyDeclaration<?>> T parseBodyDeclaration(String bd) {
        return (T) parse(() -> parser(BLEEDING_EDGE).parseBodyDeclaration(bd));
    }

    public static VariableDeclarationExpr parseVariableDeclarationExpr(String bd) {
        return parse(() -> parser(BLEEDING_EDGE).parseVariableDeclarationExpr(bd));
    }

    public static CompilationUnit parseCompilationUnit(LanguageLevel languageLevel, String stmt) {
        return parse(() -> parser(languageLevel).parse(stmt));
    }

    public static Statement parseStatement(LanguageLevel languageLevel, String stmt) {
        return parse(() -> parser(languageLevel).parseStatement(stmt));
    }

    public static <T extends Expression> T parseExpression(LanguageLevel languageLevel, String expr) {
        return parse(() -> parser(languageLevel).parseExpression(expr));
    }

    public static <T extends BodyDeclaration<?>> T parseBodyDeclaration(LanguageLevel languageLevel, String bd) {
        return (T) parse(() -> parser(languageLevel).parseBodyDeclaration(bd));
    }

    public static VariableDeclarationExpr parseVariableDeclarationExpr(LanguageLevel languageLevel, String bd) {
        return parse(() -> parser(languageLevel).parseVariableDeclarationExpr(bd));
    }
}
