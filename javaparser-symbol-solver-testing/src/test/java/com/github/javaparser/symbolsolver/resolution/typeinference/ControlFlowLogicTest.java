/*
 * Copyright (C) 2015-2016 Federico Tomassetti
 * Copyright (C) 2017-2026 The JavaParser Team.
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

package com.github.javaparser.symbolsolver.resolution.typeinference;

import static org.junit.jupiter.api.Assertions.assertThrows;

import com.github.javaparser.JavaParserAdapter;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.LocalEnumDeclarationStmt;
import org.junit.jupiter.api.Test;

class ControlFlowLogicTest {

    private final JavaParserAdapter parser = StaticJavaParser.newParserAdapter(
            new ParserConfiguration().setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_16));

    /**
     * {@code isReachable} dispatches {@link LocalEnumDeclarationStmt} to the default
     * {@code GenericVisitorAdapter} traversal (via {@code super.visit(n, arg)}), exactly like its
     * {@code LocalClassDeclarationStmt}/{@code LocalRecordDeclarationStmt} siblings. That default
     * traversal has no branch that yields a non-null {@code Boolean}, so the result is always
     * {@code null} and the {@code boolean} return type of {@code isReachable} throws a
     * {@code NullPointerException} on unboxing. This is a pre-existing limitation shared by all
     * three local-declaration statement types, not something introduced by local enum support;
     * this test documents the current behavior.
     */
    @Test
    void isReachableOnLocalEnumDeclarationStmtThrowsDueToUnimplementedTraversal() {
        CompilationUnit cu = parser.parse("class X { void m() { enum E { A, B } } }");
        LocalEnumDeclarationStmt stmt =
                cu.findFirst(LocalEnumDeclarationStmt.class).get();

        assertThrows(
                NullPointerException.class, () -> ControlFlowLogic.getInstance().isReachable(stmt));
    }

    /**
     * {@code canCompleteNormally} guards on {@code isReachable(statement)} before it can dispatch
     * to its own {@code LocalEnumDeclarationStmt} case, so it inherits the same limitation
     * documented in {@link #isReachableOnLocalEnumDeclarationStmtThrowsDueToUnimplementedTraversal()}.
     */
    @Test
    void canCompleteNormallyOnLocalEnumDeclarationStmtThrowsDueToUnimplementedTraversal() {
        CompilationUnit cu = parser.parse("class X { void m() { enum E { A, B } } }");
        LocalEnumDeclarationStmt stmt =
                cu.findFirst(LocalEnumDeclarationStmt.class).get();

        assertThrows(
                NullPointerException.class, () -> ControlFlowLogic.getInstance().canCompleteNormally(stmt));
    }
}
