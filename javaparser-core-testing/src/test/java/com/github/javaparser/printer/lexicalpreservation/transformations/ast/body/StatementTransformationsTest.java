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

package com.github.javaparser.printer.lexicalpreservation.transformations.ast.body;

import java.io.IOException;

import org.junit.jupiter.api.Test;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.printer.lexicalpreservation.AbstractLexicalPreservingTest;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;

import static com.github.javaparser.StaticJavaParser.parseStatement;

/**
 * Transforming Statement and verifying the LexicalPreservation works as expected.
 */
class StatementTransformationsTest extends AbstractLexicalPreservingTest {

    Statement consider(String code) {
        Statement statement = parseStatement(code);
        LexicalPreservingPrinter.setup(statement);
        return statement;
    }

    @Test
    void ifStmtTransformation() {
        Statement stmt = consider("if (a) {} else {}");
        stmt.asIfStmt().setCondition(new NameExpr("b"));
        assertTransformedToString("if (b) {} else {}", stmt);
    }

    @Test
    void switchEntryCsmHasTrailingUnindent() {
        Statement stmt = consider("switch (a) { case 1: a; a; }");
        NodeList<Statement> statements = stmt.asSwitchStmt().getEntry(0).getStatements();
        statements.set(1, statements.get(1).clone()); // clone() to force replacement
        assertTransformedToString("switch (a) { case 1: a; a; }", stmt);
    }

}
