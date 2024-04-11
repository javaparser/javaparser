/*
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

package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.utils.TestParser.parseStatement;
import static org.junit.jupiter.api.Assertions.assertEquals;

class BlockStmtTest {
    @Test
    void addStatementChildAtCorrectPosition() {
        BlockStmt block = parseStatement("{\nint b = 1;\nint c = 2;\n}").asBlockStmt();
        ExpressionStmt newStatement = parseStatement("int a = 0;").asExpressionStmt();
        block.addStatement(0, newStatement);

        NodeList<Statement> statements =  block.getStatements();
        List<Node> children =  block.getChildNodes();

        assertEquals(statements.size(), children.size());
        for (int i=0; i < statements.size(); i++) {
            assertEquals(statements.get(i), children.get(i));
        }
    }
}
