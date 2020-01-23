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
import org.javaparser.ast.expr.ArrayCreationExpr;
import org.javaparser.ast.expr.Expression;
import org.javaparser.ast.stmt.Statement;
import org.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.javaparser.ParseStart.*;
import static org.javaparser.ParserConfiguration.LanguageLevel.JAVA_1_0;
import static org.javaparser.Providers.provider;
import static org.javaparser.utils.TestUtils.assertNoProblems;
import static org.javaparser.utils.TestUtils.assertProblems;
import static org.junit.jupiter.api.Assertions.assertEquals;

class Java1_0ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_1_0));

    @Test
    void tryWithoutResources() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("try(X x=new Y()){}"));
        assertProblems(result,
                "(line 1,col 1) Catch with resource is not supported.",
                "(line 1,col 1) Try has no finally and no catch.");
    }

    @Test
    void classExtendingMoreThanOne() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X extends Y, Z {}"));
        assertProblems(result, "(line 1,col 20) A class cannot extend more than one other class.");
    }

    @Test
    void interfaceUsingImplements() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X implements Y {}"));
        assertProblems(result, "(line 1,col 24) An interface cannot implement other interfaces.");
    }

    @Test
    void interfaceWithInitializer() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("interface X {{}}"));
        assertProblems(result, "(line 1,col 14) An interface cannot have initializers.");
    }

    @Test
    void defaultInClass() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X {default void a(){};}"));
        assertProblems(result, "(line 1,col 10) 'default' is not allowed here.");
    }

    @Test
    void leftHandAssignmentCannotBeAConditional() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("(1==2)=3"));
        assertProblems(result, "(line 1,col 1) Illegal left hand side of an assignment.");
    }

    @Test
    void leftHandAssignmentCannotBeEmptyBraces() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("()=3"));
        assertProblems(result,
                "(line 1,col 1) Illegal left hand side of an assignment.",
                "(line 1,col 1) Lambdas are not supported.");
    }

    @Test
    void leftHandAssignmentCanBeInBraces() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("(i) += (i) += 1"));
        assertNoProblems(result);
    }

    @Test
    void noInnerClasses() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X{class Y{}}"));
        assertProblems(result, "(line 1,col 9) inner classes or interfaces are not supported.");
    }

    @Test
    void noReflection() {
        ParseResult<Expression> result = javaParser.parse(EXPRESSION, provider("Abc.class"));
        assertProblems(result, "(line 1,col 1) Reflection is not supported.");
    }

    @Test
    void nonEmptyList() {
        ArrayCreationExpr expr = new ArrayCreationExpr(PrimitiveType.booleanType());
        List<Problem> problems = new ArrayList<>();
        new Java1_0Validator().accept(expr, new ProblemReporter(problems::add));
        assertEquals("ArrayCreationExpr.levels can not be empty.", problems.get(0).getMessage());
    }

    @Test
    void noForEach() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for(X x : xs){}"));
        assertProblems(result, "(line 1,col 1) For-each loops are not supported.");
    }

    @Test
    void labelBreakAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3: break bla;}"));
        assertNoProblems(result);
    }

    @Test
    void emptyBreakAllowed() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("switch(x){case 3: break;}"));
        assertNoProblems(result);
    }
}
