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

package com.github.javaparser.ast.validator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.ParseStart.*;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_1_4;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;

class Java1_4ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_1_4));

    @Test
    void yesAssert() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("assert a;"));
        assertNoProblems(result);
    }

    @Test
    void noGenerics() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("class X<A>{List<String> b;}"));
        assertProblems(result,
                "(line 1,col 12) Generics are not supported.",
                "(line 1,col 1) Generics are not supported."
        );
    }

    @Test
    void noAnnotations() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("@Abc @Def() @Ghi(a=3) @interface X{}"));
        assertProblems(result,
                "(line 1,col 6) Annotations are not supported.",
                "(line 1,col 13) Annotations are not supported.",
                "(line 1,col 1) Annotations are not supported."
        );
    }

    @Test
    void novarargs() {
        ParseResult<Parameter> result = javaParser.parse(PARAMETER, provider("String... x"));
        assertProblems(result, "(line 1,col 1) Varargs are not supported.");
    }

    @Test
    void noforeach() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for(X x: xs){}"));
        assertProblems(result, "(line 1,col 1) For-each loops are not supported.");
    }

    @Test
    void staticImport() {
        ParseResult<CompilationUnit> result = javaParser.parse(COMPILATION_UNIT, provider("import static x;import static x.*;import x.X;import x.*;"));
        assertProblems(result,
                "(line 1,col 17) Static imports are not supported.",
                "(line 1,col 1) Static imports are not supported.");
    }

    @Test
    void enumAllowedAsIdentifier() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int enum;"));
        assertNoProblems(result);
    }
}
