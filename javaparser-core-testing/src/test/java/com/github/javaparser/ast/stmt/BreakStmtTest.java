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

package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.expr.SimpleName;
import org.junit.jupiter.api.Test;

import java.util.Optional;

import static com.github.javaparser.utils.TestParser.parseStatement;
import static org.junit.jupiter.api.Assertions.*;

class BreakStmtTest {

    @Test
    void simpleBreak() {
        BreakStmt statement = parseStatement("break;").asBreakStmt();
        assertFalse(statement.getLabel().isPresent());
    }

    @Test
    void breakWithLabel() {
        BreakStmt statement = parseStatement("break hond;").asBreakStmt();
        assertEquals("hond", statement.getLabel().get().asString());
    }

    @Test
    void constructor_simpleBreakWithoutLabel() {
        BreakStmt statement = new BreakStmt();
        assertFalse(statement.getLabel().isPresent());
        assertEquals("break;", statement.toString());
    }

    @Test
    void constructor_simpleBreakWithLabel() {
        BreakStmt statement = new BreakStmt("customLabel");
        assertTrue(statement.getLabel().isPresent());
    }

    @Test
    void constructor_simpleBreakWithSimpleNameLabel() {
        SimpleName label = new SimpleName("customLabel");
        BreakStmt statement = new BreakStmt(label);
        assertTrue(statement.getLabel().isPresent());
        assertEquals(label, statement.getLabel().get());
    }

    @Test
    void removeLabel_shouldRemoveTheLabel() {
        BreakStmt statement = new BreakStmt("customLabel");
        assertTrue(statement.getLabel().isPresent());

        statement.removeLabel();
        assertFalse(statement.getLabel().isPresent());
    }

    @Test
    void isBreakStmt_shouldBeTrue() {
        assertTrue(new BreakStmt().isBreakStmt());
    }

    @Test
    void asBreakStmt_shouldBeSame() {
        BreakStmt breakStatement = new BreakStmt();
        assertSame(breakStatement, breakStatement.asBreakStmt());
    }

    @Test
    void toBreakStmt_shouldBePresentAndBeTheSame() {
        BreakStmt breakStatement = new BreakStmt();
        Optional<BreakStmt> optBreak = breakStatement.toBreakStmt();
        assertTrue(optBreak.isPresent());
        assertSame(breakStatement, optBreak.get());
    }

    @Test
    void clone_shouldNotBeTheSameButShouldBeEquals() {
        BreakStmt breakStatement = new BreakStmt();
        BreakStmt clonedStatement = breakStatement.clone();
        assertNotSame(breakStatement, clonedStatement);
        assertEquals(breakStatement, clonedStatement);
    }

    @Test
    void remove_whenLabelIsPassedAsArgumentItShouldBeRemoved() {
        BreakStmt breakStatement = new BreakStmt("Label");
        assertTrue(breakStatement.getLabel().isPresent());

        SimpleName label = breakStatement.getLabel().get();
        assertTrue(breakStatement.remove(label));
        assertFalse(breakStatement.getLabel().isPresent());
    }

    @Test
    void replace_testReplaceLabelWithNewOne() {
        SimpleName originalLabel = new SimpleName("original");
        SimpleName replacementLabel = new SimpleName("replacement");

        BreakStmt breakStatement = new BreakStmt(originalLabel);
        assertTrue(breakStatement.getLabel().isPresent());
        assertSame(originalLabel, breakStatement.getLabel().get());

        breakStatement.replace(originalLabel, replacementLabel);
        assertTrue(breakStatement.getLabel().isPresent());
        assertSame(replacementLabel, breakStatement.getLabel().get());
    }

}
