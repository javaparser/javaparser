/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

package com.github.javaparser.issues;

import static org.junit.jupiter.api.Assertions.assertEquals;

import com.github.javaparser.Range;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.SimpleName;
import com.github.javaparser.printer.lexicalpreservation.LexicalPreservingPrinter;
import org.junit.jupiter.api.Test;

public class Issue2310Test {

    /**
     * The identifier's range must equal the range of its single IDENTIFIER token,
     * and must NOT be extended to include trailing array brackets. This holds for
     * every caller of VariableDeclaratorId(): method parameters, multi-dimensional
     * arrays, arrays with type annotations, fields, local variables, and the
     * already-correct catch parameter (control case).
     */
    @Test
    public void nameRangeMatchesIdentifierTokenForCStyleArray() {
        String[] samples = {
            "class A { void m(String args[]) {} }",
            "class A { void m(String args[][]) {} }",
            "class A { void m(int @Foo [] args @Bar []) {} }",
            "class A { int args[]; }",
            "class A { void m() { int args[] = null; } }",
            "class A { void m() { try {} catch (Exception args) {} } }"
        };
        for (String code : samples) {
            CompilationUnit cu = StaticJavaParser.parse(code);
            SimpleName name = cu.findAll(SimpleName.class).stream()
                    .filter(n -> n.getIdentifier().equals("args"))
                    .findFirst()
                    .orElseThrow(() -> new AssertionError("args SimpleName not found in: " + code));

            Range nodeRange = name.getRange().orElseThrow(() -> new AssertionError("name has no range: " + code));
            Range tokenRange = name.getTokenRange()
                    .orElseThrow(() -> new AssertionError("name has no token range: " + code))
                    .getBegin()
                    .getRange()
                    .orElseThrow(() -> new AssertionError("token has no range: " + code));

            assertEquals(
                    tokenRange,
                    nodeRange,
                    "Name range should equal its single identifier token (no array brackets) for: " + code);
        }
    }

    /**
     * Before the fix, renaming a C-style array local variable through the
     * LexicalPreservingPrinter threw an UnsupportedOperationException because the
     * '[' ']' tokens were wrongly attached to the SimpleName. After the fix the
     * rename is preserved lexically.
     */
    @Test
    public void lexicalPreservingRenameOfCStyleArrayLocalWorks() {
        CompilationUnit cu =
                LexicalPreservingPrinter.setup(StaticJavaParser.parse("class A { void m() { int loc[] = null; } }"));
        cu.findFirst(VariableDeclarator.class).get().getName().setIdentifier("renamed");
        assertEquals("class A { void m() { int renamed[] = null; } }", LexicalPreservingPrinter.print(cu));
    }
}
