/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2019 The JavaParser Team.
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

package org.javaparser.ast.validator;

import org.javaparser.JavaParser;
import org.javaparser.ParseResult;
import org.javaparser.ParserConfiguration;
import org.javaparser.Problem;
import org.javaparser.ast.CompilationUnit;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.stmt.Statement;
import org.javaparser.ast.type.ClassOrInterfaceType;
import org.javaparser.ast.type.UnionType;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.javaparser.ParseStart.COMPILATION_UNIT;
import static org.javaparser.ParseStart.EXPRESSION;
import static org.javaparser.ParseStart.STATEMENT;
import static org.javaparser.ParserConfiguration.LanguageLevel.*;
import static org.javaparser.Providers.provider;
import static org.javaparser.utils.TestUtils.assertNoProblems;
import static org.javaparser.utils.TestUtils.assertProblems;

class Java7ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_7));

    @Test
    void generics() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X<A>{List<String> b = new ArrayList<>();}"));
        assertNoProblems(result);
    }

    @Test
    void defaultMethodWithoutBody() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X {default void a();}"));
        assertProblems(result, "(line 1,col 14) 'default' is not allowed here.");
    }

    @Test
    void tryWithoutAnything() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try{}"));
        assertProblems(result, "(line 1,col 1) Try has no finally, no catch, and no resources.");
    }

    @Test
    void tryWithResourceVariableDeclaration() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try(Reader r = new Reader()){}"));
        assertNoProblems(result);
    }

    @Test
    void tryWithResourceReference() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try(a.b.c){}"));
        assertProblems(result, "(line 1,col 1) Try with resources only supports variable declarations.");
    }

    @Test
    void stringsInSwitch() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case \"abc\": ;}"));
        assertNoProblems(result);
    }

    @Test
    void binaryIntegerLiterals() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("0b01"));
        assertNoProblems(result);
    }

    @Test
    void underscoresInIntegerLiterals() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("1_000_000"));
        assertNoProblems(result);
    }

    @Test
    void multiCatch() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try{}catch(Abc|Def e){}"));
        assertNoProblems(result);
    }

    @Test
    void multiCatchWithoutElements() {
        UnionType unionType = new UnionType();

        List<Problem> problems = new ArrayList<>();
        new Java7Validator().accept(unionType, new ProblemReporter(problems::add));
        
        assertProblems(problems, "UnionType.elements can not be empty.");
    }

    @Test
    void multiCatchWithOneElement() {
        UnionType unionType = new UnionType();
        unionType.getElements().add(new ClassOrInterfaceType());

        List<Problem> problems = new ArrayList<>();
        new Java7Validator().accept(unionType, new ProblemReporter(problems::add));
        
        assertProblems(problems, "Union type (multi catch) must have at least two elements.");
    }

    @Test
    void noLambdas() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("a(() -> 1);"));
        assertProblems(result, "(line 1,col 3) Lambdas are not supported.");
    }
}
