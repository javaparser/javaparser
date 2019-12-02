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

package com.github.javaparser.ast.nodeTypes;

import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.utils.TestParser;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class NodeWithBodyTest {
    @Test
    void emptyStatementIsEmpty() {
        ForStmt forStmt = TestParser.parseStatement("for(;;);").asForStmt();

        assertTrue(forStmt.hasEmptyBody());
    }

    @Test
    void emptyBlockIsEmpty() {
        ForStmt forStmt = TestParser.parseStatement("for(;;){}").asForStmt();

        assertTrue(forStmt.hasEmptyBody());
    }

    @Test
    void simpleStatementIsNotEmpty() {
        ForStmt forStmt = TestParser.parseStatement("for(;;)a=b;").asForStmt();

        assertFalse(forStmt.hasEmptyBody());
    }

    @Test
    void nonEmptyBlockIsNotEmpty() {
        ForStmt forStmt = TestParser.parseStatement("for(;;){a=b;}").asForStmt();

        assertFalse(forStmt.hasEmptyBody());
    }
}
