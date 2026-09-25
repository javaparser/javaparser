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

package com.github.javaparser.ast.validator;

import static com.github.javaparser.ParseStart.*;
import static com.github.javaparser.ParserConfiguration.LanguageLevel.JAVA_1_4;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static com.github.javaparser.utils.TestUtils.assertProblems;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

class Java1_4ValidatorTest {
    public static final JavaParser javaParser = new JavaParser(new ParserConfiguration().setLanguageLevel(JAVA_1_4));

    @Test
    void yesAssert() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("assert a;"));
        assertNoProblems(result);
    }

    @Test
    void assertIsNotValideIdentifierSinceJAVA_1_4() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("String assert;"));
        assertProblems(
                result,
                "(line 1,col 8) 'assert' identifier is not supported. Pay attention that this feature is no longer supported since 'JAVA_1_4' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.");
    }

    @Test
    void noGenerics() {
        ParseResult<CompilationUnit> result =
                javaParser.parse(COMPILATION_UNIT, provider("class X<A>{List<String> b;}"));
        assertProblems(
                result,
                "(line 1,col 1) Generics are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.",
                "(line 1,col 12) Generics are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.");
    }

    @Test
    void noAnnotations() {
        ParseResult<CompilationUnit> result =
                javaParser.parse(COMPILATION_UNIT, provider("@Abc @Def() @Ghi(a=3) @interface X{}"));
        assertProblems(
                result,
                "(line 1,col 13) Annotations are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.",
                "(line 1,col 1) Annotations are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.",
                "(line 1,col 6) Annotations are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.");
    }

    @Test
    void novarargs() {
        ParseResult<Parameter> result = javaParser.parse(PARAMETER, provider("String... x"));
        assertProblems(
                result,
                "(line 1,col 1) Varargs are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.");
    }

    @Test
    void noforeach() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("for(X x: xs){}"));
        assertProblems(
                result,
                "(line 1,col 1) For-each loops are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.");
    }

    @Test
    void staticImport() {
        ParseResult<CompilationUnit> result = javaParser.parse(
                COMPILATION_UNIT, provider("import static x;import static x.*;import x.X;import x.*;"));
        assertProblems(
                result,
                "(line 1,col 1) Static imports are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.",
                "(line 1,col 17) Static imports are not supported. Pay attention that this feature is supported starting from 'JAVA_5' language level. If you need that feature the language level must be configured in the configuration before parsing the source files.");
    }

    @Test
    void enumAllowedAsIdentifier() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("int enum;"));
        assertNoProblems(result);
    }

    /**
     * A statement beginning with `enum` must stay parsable as an identifier, matching the
     * pre-Java-5 `Enumeration enum = ...; enum.hasMoreElements();` idiom. The local-enum-declaration
     * lookahead in BlockStatement() must not greedily commit these to EnumDeclaration().
     */
    @Test
    void enumAssignmentAllowedAsIdentifier() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("enum = 3;"));
        assertNoProblems(result);
        ExpressionStmt stmt = result.getResult().get().asExpressionStmt();
        AssignExpr assign = stmt.getExpression().asAssignExpr();
        assertEquals("enum", assign.getTarget().asNameExpr().getNameAsString());
    }

    @Test
    void enumMethodCallAllowedAsIdentifier() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("enum.hasMoreElements();"));
        assertNoProblems(result);
        ExpressionStmt stmt = result.getResult().get().asExpressionStmt();
        MethodCallExpr call = stmt.getExpression().asMethodCallExpr();
        assertEquals("enum", call.getScope().get().asNameExpr().getNameAsString());
    }

    @Test
    void enumTypedVariableAllowedAsIdentifier() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("enum x = null;"));
        assertNoProblems(result);
        ExpressionStmt stmt = result.getResult().get().asExpressionStmt();
        VariableDeclarationExpr vde = stmt.getExpression().asVariableDeclarationExpr();
        assertEquals("enum", vde.getElementType().asString());
        assertEquals("x", vde.getVariable(0).getNameAsString());
    }

    @Test
    void enumArrayAccessAllowedAsIdentifier() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("enum[0] = 1;"));
        assertNoProblems(result);
        ExpressionStmt stmt = result.getResult().get().asExpressionStmt();
        AssignExpr assign = stmt.getExpression().asAssignExpr();
        ArrayAccessExpr arrayAccess = assign.getTarget().asArrayAccessExpr();
        assertEquals("enum", arrayAccess.getName().asNameExpr().getNameAsString());
    }

    @Test
    void enumIncrementAllowedAsIdentifier() {
        ParseResult<Statement> result = javaParser.parse(STATEMENT, provider("enum++;"));
        assertNoProblems(result);
        ExpressionStmt stmt = result.getResult().get().asExpressionStmt();
        UnaryExpr unary = stmt.getExpression().asUnaryExpr();
        assertEquals("enum", unary.getExpression().asNameExpr().getNameAsString());
        assertTrue(unary.getOperator() == UnaryExpr.Operator.POSTFIX_INCREMENT);
    }

    @Test
    void enumUsedAsIdentifierInFullIdiom() {
        ParseResult<CompilationUnit> result = javaParser.parse(
                COMPILATION_UNIT,
                provider("class X { void m() { Enumeration enum = elements(); enum.hasMoreElements(); } }"));
        assertNoProblems(result);
    }
}
