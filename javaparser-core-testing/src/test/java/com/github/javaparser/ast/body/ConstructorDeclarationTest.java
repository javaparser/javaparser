/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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

package com.github.javaparser.ast.body;

import static com.github.javaparser.ParseStart.COMPILATION_UNIT;
import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.utils.TestUtils.assertNoProblems;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.utils.LineSeparator;
import org.junit.jupiter.api.Test;

class ConstructorDeclarationTest {
    @Test
    void acceptsSuper() {
        ConstructorDeclaration cons = new ConstructorDeclaration("Cons");
        cons.createBody().addStatement("super();");

        assertEquals(
                String.format("public Cons() {%1$s" + "    super();%1$s" + "}", LineSeparator.SYSTEM), cons.toString());
    }

    @Test
    void explicitConstructorInvocationAfterFirstStatement() {
        String code = "class Foo {\n" + "    public Foo() {\n"
                + "        int x = 2;\n"
                + "        super();\n"
                + "        x = 3;\n"
                + "    }\n"
                + "}";

        ParserConfiguration configuration =
                new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_25);
        JavaParser parser = new JavaParser(configuration);
        ParseResult<CompilationUnit> result = parser.parse(COMPILATION_UNIT, provider(code));
        assertNoProblems(result);

        CompilationUnit cu = result.getResult().get();

        ConstructorDeclaration constructorDeclaration =
                Navigator.demandNodeOfGivenClass(cu, ConstructorDeclaration.class);
        NodeList<Statement> statements = constructorDeclaration.getBody().get().getStatements();

        assertTrue(statements.get(0).isExpressionStmt());
        assertTrue(statements.get(0).asExpressionStmt().getExpression().isVariableDeclarationExpr());
        assertTrue(statements.get(1).isExplicitConstructorInvocationStmt());
        assertFalse(statements.get(1).asExplicitConstructorInvocationStmt().isThis());
        assertTrue(statements.get(2).isExpressionStmt());
        assertTrue(statements.get(2).asExpressionStmt().getExpression().isAssignExpr());
    }
}
