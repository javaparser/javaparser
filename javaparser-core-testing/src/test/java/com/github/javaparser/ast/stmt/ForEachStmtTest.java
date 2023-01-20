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

import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.StaticJavaParser.parseStatement;
import static org.junit.jupiter.api.Assertions.*;

class ForEachStmtTest {
    @Test
    void nonFinalPrimitive() {
        ForEachStmt statement = parseStatement("for (int i : ints) {}").asForEachStmt();
        assertFalse(statement.hasFinalVariable());
        assertEquals(PrimitiveType.intType(), statement.getVariableDeclarator().getType());
        assertEquals("i", statement.getVariableDeclarator().getName().getIdentifier());
    }

    @Test
    void finalNonPrimitive() {
        ForEachStmt statement = parseStatement("for (final Object o : objs) {}").asForEachStmt();
        assertTrue(statement.hasFinalVariable());
        assertEquals(new ClassOrInterfaceType(null, "Object"), statement.getVariableDeclarator().getType());
        assertEquals("o", statement.getVariableDeclarator().getName().getIdentifier());
    }
}
