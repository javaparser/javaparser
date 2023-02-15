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

package com.github.javaparser.utils;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.Statement;

import java.util.HashMap;
import java.util.Map;

import static com.github.javaparser.ParserConfiguration.LanguageLevel;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.BLEEDING_EDGE;
import static org.junit.jupiter.api.Assertions.fail;

public class TestParser {

    private static final Map<LanguageLevel, JavaParser> parserCache = new HashMap<>();

    private static JavaParser parser(LanguageLevel languageLevel) {
        return parserCache.computeIfAbsent(languageLevel, ll -> new JavaParser(new ParserConfiguration().setLanguageLevel(ll)));
    }

    private static <T> T unpack(ParseResult<T> result) {
        if (!result.isSuccessful()) {
            fail(result.getProblems().toString());
        }
        return result.getResult().get();
    }

    public static CompilationUnit parseCompilationUnit(String stmt) {
        return unpack(parser(BLEEDING_EDGE).parse(stmt));
    }

    public static Statement parseStatement(String stmt) {
        return unpack(parser(BLEEDING_EDGE).parseStatement(stmt));
    }

    public static <T extends Expression> T parseExpression(String expr) {
        return unpack(parser(BLEEDING_EDGE).parseExpression(expr));
    }

    public static <T extends BodyDeclaration<?>> T parseBodyDeclaration(String bd) {
        return (T) unpack(parser(BLEEDING_EDGE).parseBodyDeclaration(bd));
    }

    public static VariableDeclarationExpr parseVariableDeclarationExpr(String bd) {
        return unpack(parser(BLEEDING_EDGE).parseVariableDeclarationExpr(bd));
    }

    public static CompilationUnit parseCompilationUnit(LanguageLevel languageLevel, String stmt) {
        return unpack(parser(languageLevel).parse(stmt));
    }

    public static Statement parseStatement(LanguageLevel languageLevel, String stmt) {
        return unpack(parser(languageLevel).parseStatement(stmt));
    }

    public static <T extends Expression> T parseExpression(LanguageLevel languageLevel, String expr) {
        return unpack(parser(languageLevel).parseExpression(expr));
    }

    public static <T extends BodyDeclaration<?>> T parseBodyDeclaration(LanguageLevel languageLevel, String bd) {
        return (T) unpack(parser(languageLevel).parseBodyDeclaration(bd));
    }

    public static VariableDeclarationExpr parseVariableDeclarationExpr(LanguageLevel languageLevel, String bd) {
        return unpack(parser(languageLevel).parseVariableDeclarationExpr(bd));
    }
}
