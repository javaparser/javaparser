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
package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test suite for LEFTOVER rules in Difference.apply()
 *
 * Covers handling of remaining elements after main processing completes.
 * These rules handle edge cases where diff or original lists have leftover elements.
 */
class DifferenceApplyLeftoverRulesTest extends AbstractLexicalPreservingTest {

    // =========================================================================
    // L1: LeftOver.Diff.Kept
    // =========================================================================

    @Test
    void l1_skipLeftoverKeptElements() {
        considerCode(
            "class X {\n" +
            "    int field;\n" +
            "}"
        );

        ClassOrInterfaceDeclaration clazz = cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Simple modification that processes all elements
        clazz.getFieldByName("field").get().getVariable(0).setName("data");

        String expected =
            "class X {\n" +
            "    int data;\n" +
            "}";

        // Should not fail even if there are kept elements at the end
        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // L2: LeftOver.Diff.Added.Indent
    // =========================================================================

    @Test
    void l2_processLeftoverIndentDirective() {
        considerCode(
            "class X {\n" +
            "    void method() {\n" +
            "        int x = 1;\n" +
            "    }\n" +
            "}"
        );

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement at end (may have leftover indent directive)
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int y = 2;").asExpressionStmt();
        body.getStatements().add(newStmt);

        String expected =
            "class X {\n" +
            "    void method() {\n" +
            "        int x = 1;\n" +
            "        int y = 2;\n" +
            "    }\n" +
            "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // L3: LeftOver.Diff.Added.Unindent
    // =========================================================================

    @Test
    void l3_processLeftoverUnindentDirective() {
        considerCode(
            "class X {\n" +
            "    void method() {\n" +
            "        if (true) {\n" +
            "            int x = 1;\n" +
            "        }\n" +
            "    }\n" +
            "}"
        );

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement after if (may have leftover unindent)
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int y = 2;").asExpressionStmt();
        body.getStatements().add(newStmt);

        String expected =
            "class X {\n" +
            "    void method() {\n" +
            "        if (true) {\n" +
            "            int x = 1;\n" +
            "        }\n" +
            "        int y = 2;\n" +
            "    }\n" +
            "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // L4: LeftOver.Diff.Added.Element
    // =========================================================================

    @Test
    void l4_addLeftoverElements() {
        considerCode(
            "class X {\n" +
            "    void method() {\n" +
            "        int x = 1;\n" +
            "    }\n" +
            "}"
        );

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add multiple statements (some may be leftover)
        body.getStatements().add(StaticJavaParser.parseStatement("int y = 2;").asExpressionStmt());
        body.getStatements().add(StaticJavaParser.parseStatement("int z = 3;").asExpressionStmt());

        String expected =
            "class X {\n" +
            "    void method() {\n" +
            "        int x = 1;\n" +
            "        int y = 2;\n" +
            "        int z = 3;\n" +
            "    }\n" +
            "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // L5: LeftOver.Diff.Removed
    // =========================================================================

    @Test
    void l5_skipLeftoverRemovedElements() {
        considerCode(
            "class X {\n" +
            "    int a;\n" +
            "    int b;\n" +
            "    int c;\n" +
            "}"
        );

        ClassOrInterfaceDeclaration clazz = cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Remove multiple fields
        clazz.getMembers().remove(2); // Remove c
        clazz.getMembers().remove(1); // Remove b

        String expected =
            "class X {\n" +
            "    int a;\n" +
            "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // L6: LeftOver.Original.WhiteSpaceOrComment
    // =========================================================================

    @Test
    void l6_preserveLeftoverWhitespaceAndComments() {
        considerCode(
            "class X {\n" +
            "    int field;\n" +
            "    // trailing comment\n" +
            "}"
        );

        ClassOrInterfaceDeclaration clazz = cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Modify field (trailing comment should be preserved)
        clazz.getFieldByName("field").get().getVariable(0).setName("data");

        String expected =
            "class X {\n" +
            "    int data;\n" +
            "    // trailing comment\n" +
            "}";

        assertTransformedToString(expected, cu);
    }

    @Test
    void l6_preserveTrailingWhitespace() {
        considerCode(
            "class X {\n" +
            "    int field;\n" +
            "\n" +
            "}"
        );

        ClassOrInterfaceDeclaration clazz = cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Modify field (trailing newline should be preserved)
        clazz.getFieldByName("field").get().getVariable(0).setName("data");

        String result = print();

        assertTrue(result.contains("int data"), "Field should be modified");
        // Trailing structure should be preserved
        assertTrue(result.endsWith("}\n") || result.endsWith("}"), "Class should end properly");
    }

    // =========================================================================
    // L7: LeftOver.Original.Other (Exception case)
    // =========================================================================

    @Test
    void l7_detectUnsynchronizedElements() {
        considerCode(
            "class X {\n" +
            "    int field;\n" +
            "}"
        );

        ClassOrInterfaceDeclaration clazz = cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Normal modification should not trigger exception
        clazz.getFieldByName("field").get().getVariable(0).setName("data");

        String expected =
            "class X {\n" +
            "    int data;\n" +
            "}";

        // Should complete without UnsupportedOperationException
        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // Complex scenarios with multiple leftover types
    // =========================================================================

    @Test
    void multipleLeftoverElementTypes() {
        considerCode(
            "class X {\n" +
            "    int a;\n" +
            "    int b;\n" +
            "    // comment\n" +
            "    int c;\n" +
            "}"
        );

        ClassOrInterfaceDeclaration clazz = cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Modify first field
        clazz.getFieldByName("a").get().getVariable(0).setName("alpha");

        String result = print();

        // All elements should be preserved or handled correctly
        assertTrue(result.contains("int alpha"), "Modified field should be present");
        assertTrue(result.contains("int b"), "Second field should be preserved");
        assertTrue(result.contains("// comment"), "Comment should be preserved");
        assertTrue(result.contains("int c"), "Third field should be preserved");
    }

    @Test
    void leftoverElementsAfterRemoval() {
        considerCode(
            "class X {\n" +
            "    int a;\n" +
            "    int b;\n" +
            "    int c;\n" +
            "    // final comment\n" +
            "}"
        );

        ClassOrInterfaceDeclaration clazz = cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Remove middle field
        clazz.getMembers().remove(1);

        String result = print();

        assertTrue(result.contains("int a"), "First field should remain");
        assertFalse(result.contains("int b"), "Middle field should be removed");
        assertTrue(result.contains("int c"), "Last field should remain");
        assertTrue(result.contains("// final comment"), "Trailing comment should be preserved");
    }

    @Test
    void leftoverElementsAfterAddition() {
        considerCode(
            "class X {\n" +
            "    int a;\n" +
            "    // comment\n" +
            "}"
        );

        ClassOrInterfaceDeclaration clazz = cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Add field before comment
        clazz.addField("int", "b");

        String result = print();

        assertTrue(result.contains("int a"), "First field should remain");
        assertTrue(result.contains("int b"), "New field should be added");
        assertTrue(result.contains("// comment"), "Comment should be preserved");
    }

    @Test
    void complexLeftoverScenario() {
        considerCode(
            "class X {\n" +
            "    void method() {\n" +
            "        int x = 1;\n" +
            "        // comment\n" +
            "        int y = 2;\n" +
            "    }\n" +
            "    // trailing\n" +
            "}"
        );

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement at end
        body.getStatements().add(StaticJavaParser.parseStatement("int z = 3;").asExpressionStmt());

        String result = print();

        // All original elements plus new one should be present
        assertTrue(result.contains("int x = 1"), "First statement should remain");
        assertTrue(result.contains("// comment"), "Comment should remain");
        assertTrue(result.contains("int y = 2"), "Second statement should remain");
        assertTrue(result.contains("int z = 3"), "New statement should be added");
        assertTrue(result.contains("// trailing"), "Trailing comment should remain");
    }

    // =========================================================================
    // Helper methods
    // =========================================================================

    private String print() {
        return LexicalPreservingPrinter.print(cu);
    }
}

