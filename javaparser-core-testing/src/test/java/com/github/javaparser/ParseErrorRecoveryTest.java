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

package com.github.javaparser;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.LabeledStmt;
import com.github.javaparser.ast.stmt.Statement;
import org.junit.jupiter.api.Test;

import static com.github.javaparser.Providers.provider;
import static com.github.javaparser.ast.Node.Parsedness.UNPARSABLE;
import static org.junit.jupiter.api.Assertions.assertEquals;

class ParseErrorRecoveryTest {
    private final JavaParser parser = new JavaParser();

    @Test
    void compilationUnitRecovery() {
        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, provider("XXX")).getResult().get();
        assertEquals(UNPARSABLE, cu.getParsed());
    }

    @Test
    void bodystatementSemicolonRecovery() {
        MethodDeclaration cu = parser.parse(ParseStart.CLASS_BODY, provider("int x(){X X X;}")).getResult().get().asMethodDeclaration();
        Statement xxx = cu.getBody().get().getStatements().get(0);
        assertEquals(UNPARSABLE, xxx.getParsed());
    }

    @Test
    void bodystatementClosingBraceRecovery() {
        MethodDeclaration cu = parser.parse(ParseStart.CLASS_BODY, provider("int x(){X X X}")).getResult().get().asMethodDeclaration();
        Statement xxx = cu.getBody().get();
        assertEquals(UNPARSABLE, xxx.getParsed());
    }

    @Test
    void labeledStatementSemicolonRecovery() {
        CompilationUnit cu = parser.parse(ParseStart.COMPILATION_UNIT, provider("class X{int x(){aaa:X X X;}}")).getResult().get();
        LabeledStmt xxx = cu.getClassByName("X").get().getMethods().get(0).getBody().get().getStatements().get(0).asLabeledStmt();
        assertEquals(UNPARSABLE, xxx.getStatement().getParsed());
    }
}
