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

package com.github.javaparser.ast.stmt;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.StaticJavaParser;
import org.junit.jupiter.api.Test;

class IfElseStmtTest {

    private final JavaParserAdapter parser = StaticJavaParser.newParserAdapter();

    @Test
    void issue1247withElseSingleStmt() {
        IfStmt ifStmt = parser.parseStatement("if (cond) doSomething(); else doSomethingElse();")
                .asIfStmt();
        assertFalse(ifStmt.hasElseBlock());
        assertTrue(ifStmt.hasElseBranch());
        assertFalse(ifStmt.hasCascadingIfStmt());
    }

    @Test
    void issue1247withElseBlockStmt() {
        IfStmt ifStmt = parser.parseStatement("if (cond) doSomething(); else { doSomethingElse(); }")
                .asIfStmt();
        assertTrue(ifStmt.hasElseBlock());
        assertTrue(ifStmt.hasElseBranch());
        assertFalse(ifStmt.hasCascadingIfStmt());
    }

    @Test
    void issue1247withElseSingleStmtWhichIsAnIf() {
        IfStmt ifStmt = parser.parseStatement("if (cond1) doSomething(); else if (cond2) doSomethingElse();")
                .asIfStmt();
        assertFalse(ifStmt.hasElseBlock());
        assertTrue(ifStmt.hasElseBranch());
        assertTrue(ifStmt.hasCascadingIfStmt());
    }
}
