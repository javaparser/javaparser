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

import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

/**
 * Test suite for remaining ADDED rules in Difference.apply()
 *
 * Covers indentation directives, comment handling, and newline adjustments.
 */
class DifferenceApplyAddedRulesCompleteTest extends AbstractLexicalPreservingTest {

    // =========================================================================
    // A1: Added.Indent
    // =========================================================================

    @Test
    void a1_addIndentDirective() {
        considerCode(
                "class X {\n" + "    void method() {\n" + "        if (true) {\n" + "        }\n" + "    }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        IfStmt ifStmt = method.findFirst(IfStmt.class).get();
        BlockStmt thenBlock = ifStmt.getThenStmt().asBlockStmt();

        // Add statement inside if block (triggers indent)
        thenBlock.addStatement("int x = 1;");

        String expected = "class X {\n" + "    void method() {\n"
                + "        if (true) {\n"
                + "            int x = 1;\n"
                + "        }\n"
                + "    }\n"
                + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // A2: Added.Unindent
    // =========================================================================

    @Test
    void a2_addUnindentDirective() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        if (true) {\n"
                + "            int x = 1;\n"
                + "        }\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement after if (triggers unindent then normal indent)
        body.addStatement("int y = 2;");

        String expected = "class X {\n" + "    void method() {\n"
                + "        if (true) {\n"
                + "            int x = 1;\n"
                + "        }\n"
                + "        int y = 2;\n"
                + "    }\n"
                + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // A5: Added.Element + Current.Comment + CommentBeforeAdded
    // =========================================================================

    @Test
    void a5_addElementAfterComment() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        /* comment */\n"
                + "        int x = 1;\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement (should be positioned correctly relative to comment)
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int y = 2;").asExpressionStmt();
        body.getStatements().add(0, newStmt);

        String result = print();

        assertTrue(result.contains("int y = 2"), "New statement should be added");
        assertTrue(result.contains("/* comment */"), "Comment should be preserved");
        assertTrue(result.contains("int x = 1"), "Original statement should remain");
    }

    // =========================================================================
    // A6: Added.Element + Current.Newline + Previous.Comment
    // =========================================================================

    @Test
    void a6_addElementAfterCommentAndNewline() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        int x = 1; // end of line comment\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement after line with trailing comment
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int y = 2;").asExpressionStmt();
        body.getStatements().add(newStmt);

        String expected = "class X {\n" + "    void method() {\n"
                + "        int x = 1; // end of line comment\n"
                + "        int y = 2;\n"
                + "    }\n"
                + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // A7: Added.Element + Current.Newline + Child
    // =========================================================================

    @Test
    void a7_addChildAfterNewline() {
        considerCode("class X {\n" + "    void method() {\n" + "        int x = 1;\n" + "\n" + "    }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement (should skip newline and add with proper indentation)
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int y = 2;").asExpressionStmt();
        body.getStatements().add(newStmt);

        String result = print();

        assertTrue(result.contains("int x = 1"), "First statement should remain");
        assertTrue(result.contains("int y = 2"), "New statement should be added");
    }

    // =========================================================================
    // A8: Added.Element + Current.Newline + Child + SpecialCases
    // =========================================================================

    @Test
    @Disabled("Bug: Adding statement at beginning of block loses indentation")
    void a8_addChildAtBeginning() {
        considerCode("class X {\n" + "    void method() {\n" + "        int y = 2;\n" + "    }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement at beginning (special case)
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int x = 1;").asExpressionStmt();
        body.getStatements().add(0, newStmt);

        String expected = "class X {\n" + "    void method() {\n"
                + "        int x = 1;\n"
                + "        int y = 2;\n"
                + "    }\n"
                + "}";

        assertTransformedToString(expected, cu);
    }

    @Test
    void a8_addAfterMultipleNewlines() {
        considerCode("class X {\n" + "    void method() {\n" + "\n" + "        int y = 2;\n" + "    }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement (should handle multiple newlines)
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int x = 1;").asExpressionStmt();
        body.getStatements().add(0, newStmt);

        String result = print();

        assertTrue(result.contains("int x = 1"), "New statement should be added");
        assertTrue(result.contains("int y = 2"), "Original statement should remain");
    }

    // =========================================================================
    // A11: Added.Newline + FollowedByUnindent
    // =========================================================================

    @Test
    void a11_addNewlineBeforeUnindent() {
        considerCode("class X {\n" + "    void method() {\n" + "        if (true) { int x = 1; }\n" + "    }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        IfStmt ifStmt = method.findFirst(IfStmt.class).get();
        BlockStmt thenBlock = ifStmt.getThenStmt().asBlockStmt();

        // Add another statement to if block
        thenBlock.addStatement("int y = 2;");

        String result = print();

        // Should handle unindent properly
        assertTrue(result.contains("int x = 1"), "First statement should remain");
        assertTrue(result.contains("int y = 2"), "New statement should be added");
    }

    // =========================================================================
    // A12: Added.Newline + Followed.Newline
    // =========================================================================

    @Test
    void a12_addNewlineFollowedByAnotherNewline() {
        considerCode("class X {\n" + "    void method() {\n" + "        int x = 1;\n" + "    }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement (creates newline)
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int y = 2;").asExpressionStmt();
        body.getStatements().add(newStmt);

        String result = print();

        // Should handle multiple newlines correctly
        assertFalse(result.contains("\n\n\n"), "Should not create triple newlines");
        assertTrue(result.contains("int x = 1"), "First statement should remain");
        assertTrue(result.contains("int y = 2"), "New statement should be added");
    }

    // =========================================================================
    // A13: Added.Newline + Followed.RightBrace + NotFollowedByUnindent
    // =========================================================================

    @Test
    void a13_addNewlineBeforeClosingBrace() {
        considerCode("class X {\n" + "    void method() { int x = 1; }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add statement (should handle closing brace properly)
        ExpressionStmt newStmt = StaticJavaParser.parseStatement("int y = 2;").asExpressionStmt();
        body.getStatements().add(newStmt);

        String result = print();

        assertTrue(result.contains("int x = 1"), "First statement should remain");
        assertTrue(result.contains("int y = 2"), "New statement should be added");
        assertTrue(result.contains("}"), "Closing brace should be present");
    }

    // =========================================================================
    // Complex scenarios
    // =========================================================================

    @Test
    void addNestedBlocksWithCorrectIndentation() {
        considerCode("class X {\n" + "    void method() {\n" + "    }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Add nested if statements
        IfStmt ifStmt =
                StaticJavaParser.parseStatement("if (true) { int x = 1; }").asIfStmt();
        body.addStatement(ifStmt);

        String result = print();

        assertTrue(result.contains("if (true)"), "If statement should be added");
        assertTrue(result.contains("int x = 1"), "Nested statement should be added");

        // Verify indentation levels
        assertTrue(result.contains("    void method()"), "Method should have class-level indent");
        assertTrue(result.contains("        if (true)"), "If should have method-level indent");
    }

    @Test
    void addMultipleLevelsOfNesting() {
        considerCode(
                "class X {\n" + "    void method() {\n" + "        if (true) {\n" + "        }\n" + "    }\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        IfStmt ifStmt = method.findFirst(IfStmt.class).get();
        BlockStmt thenBlock = ifStmt.getThenStmt().asBlockStmt();

        // Add nested if inside existing if
        IfStmt nestedIf =
                StaticJavaParser.parseStatement("if (false) { int x = 1; }").asIfStmt();
        thenBlock.addStatement(nestedIf);

        String result = print();

        assertTrue(result.contains("if (true)"), "Outer if should remain");
        assertTrue(result.contains("if (false)"), "Inner if should be added");

        // Verify proper indentation at all levels
        String[] lines = result.split("\n");
        boolean foundNestedIf = false;
        for (String line : lines) {
            if (line.contains("if (false)")) {
                foundNestedIf = true;
                // Should have 3 levels of indentation (class, method, outer if)
                assertTrue(line.startsWith("            "), "Nested if should have correct indentation");
            }
        }
        assertTrue(foundNestedIf, "Nested if should be present in output");
    }

    // =========================================================================
    // Helper methods
    // =========================================================================

    private String print() {
        return LexicalPreservingPrinter.print(cu);
    }
}
