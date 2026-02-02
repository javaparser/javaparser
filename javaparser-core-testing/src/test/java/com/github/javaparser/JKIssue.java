/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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
import java.io.IOException;
import java.nio.file.Paths;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class JKIssue {
    @Test
    void test() throws IOException {
        ParserConfiguration cfg = new ParserConfiguration();
        cfg.setProcessJml(true);
        JavaParser parser = new JavaParser(cfg);
        CompilationUnit cu = parser.parse(Paths.get("src/test/test_sourcecode/JKIssueDoubleContract.java"))
                .getResult()
                .get();

        var methods = cu.getPrimaryType().get().getMethods();
        for (var method : methods) {
            Assertions.assertEquals(1, method.getContracts().size());
        }
    }

    @Test
    void test2() throws IOException {
        ParserConfiguration cfg = new ParserConfiguration();
        cfg.setProcessJml(true);
        JavaParser parser = new JavaParser(cfg);
        CompilationUnit cu = parser.parse(Paths.get("src/test/test_sourcecode/MissingParentSimpleExprClause.java"))
                .getResult()
                .get();

        var clause = cu.getType(0)
                .getMethods()
                .get(0)
                .getContracts()
                .get(0)
                .getClauses()
                .get(0)
                .asJmlSimpleExprClause();
        Assertions.assertEquals(1, clause.getChildNodes().size());
    }

    @Test
    void test3() throws IOException {
        ParserConfiguration cfg = new ParserConfiguration();
        cfg.setProcessJml(true);
        JavaParser parser = new JavaParser(cfg);
        final var result = parser.parse(Paths.get("src/test/test_sourcecode/JKTmpTest.java"));
        result.getProblems().forEach(System.err::println);
        Assertions.assertTrue(result.isSuccessful());
    }
}
