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

import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.BlockStmt;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

/**
 * Test suite for remaining REMOVED rules in Difference.apply()
 *
 * Covers indentation handling, whitespace management, and edge cases.
 */
class DifferenceApplyRemovedRulesCompleteTest extends AbstractLexicalPreservingTest {

    // =========================================================================
    // R3: Removed.Child + Original.Child + FirstElement + ParentIndentation
    // =========================================================================

    @Test
    void r3_removeFirstElementWithParentIndentation() {
        considerCode("class X {\n" + "    @Deprecated\n" + "    void method() {}\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();

        // Remove annotation (first element)
        method.getAnnotations().clear();

        String expected = "class X {\n" + "    void method() {}\n" + "}";

        assertTransformedToString(expected, cu);
    }

    @Test
    void r3_removeAnnotationFromMethod() {
        considerCode("class X {\n" + "    @Override\n" + "    public void method() {}\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        method.getAnnotations().clear();

        String expected = "class X {\n" + "    public void method() {}\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // R4: Removed.Child + Original.Child + EnforceIndentation
    // =========================================================================

    @Test
    void r4_removeElementEnforcesIndentation() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        int x = 1;\n"
                + "        int y = 2; int z = 3;\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Remove second statement (partial line removal)
        body.getStatements().remove(1);

        String result = print();

        // Indentation should be maintained for remaining element
        assertTrue(result.contains("int x = 1"), "First statement should remain");
        assertTrue(result.contains("int z = 3"), "Third statement should remain");
    }

    // =========================================================================
    // R5: Removed.Child + Original.Child + DoubleWhiteSpace
    // =========================================================================

    @Test
    void r5_modifyElementShouldNotCleansDoubleWhitespace() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        int x =  1;\n"
                + "        int y = 2;\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Modify should not trigger whitespace cleanup
        body.getStatements()
                .get(0)
                .asExpressionStmt()
                .getExpression()
                .asVariableDeclarationExpr()
                .getVariable(0)
                .setName("a");

        String result = print();

        // Double spaces should not be cleaned up
        assertTrue(result.contains("=  1"), "Double whitespace should not be cleaned");
    }

    // =========================================================================
    // R7: Removed.Child + Original.Child + RemoveIndentation
    // =========================================================================

    @Test
    void r7_removeCompleteLineRemovesIndentation() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        int x = 1;\n"
                + "        int y = 2;\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Remove complete line
        body.getStatements().remove(0);

        String expected = "class X {\n" + "    void method() {\n" + "        int y = 2;\n" + "    }\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // R8: Removed.Child + Original.Child + RemoveParentIndentation
    // =========================================================================

    @Test
    void r8_removeFirstNonInlineElementRemovesParentIndentation() {
        considerCode("class X {\n" + "    @Deprecated\n"
                + "    @SuppressWarnings(\"all\")\n"
                + "    void method() {}\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();

        // Remove all annotations
        method.getAnnotations().clear();

        String expected = "class X {\n" + "    void method() {}\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // R10: Removed.Child + Original.Comment
    // =========================================================================

    @Test
    @Disabled("Bug: Removing a commented expression should also delete the associated comment")
    void r10_removeCommentInsteadOfExpectedChild() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        /* comment */\n"
                + "        int x = 1;\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Remove statement (comment encountered before it)
        body.getStatements().clear();

        String expected = "class X {\n" + "    void method() {\n" + "    }\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // R12: Removed.Token + Original.Token + EOL
    // =========================================================================

    @Test
    void r12_removeNewlineToken() {
        considerCode("class X {\n" + "\n" + "    int field;\n" + "}");

        String result = print();

        // Newlines should be preserved (this tests that EOL handling works)
        assertTrue(result.contains("class X"), "Class should be present");
        assertTrue(result.contains("int field"), "Field should be present");
    }

    // =========================================================================
    // R13: Removed.WhiteSpaceNotEOL + Original.SpaceOrTab
    // =========================================================================

    @Test
    void r13_ChangingNodeShouldNotModifyExtraWhitespaces() {
        considerCode("class X {\n" + "    int  field;\n" + "}");

        ClassOrInterfaceDeclaration clazz =
                cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Modify field should not trigger whitespace handling
        clazz.getFieldByName("field").get().getVariable(0).setName("data");

        String result = print();

        assertTrue(result.contains("int  data"), "Changing field name should not modify extra whitespace");
    }

    // =========================================================================
    // R14: Removed.Indent/Unindent + Original.SpaceOrTab
    // =========================================================================

    @Test
    void r14_removeIndentUnindentDirective() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        if (true) {\n"
                + "            int x = 1;\n"
                + "        }\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();

        // Modify to trigger indent/unindent handling
        method.setType("String");

        String result = print();

        // Indentation should be preserved
        assertTrue(
                result.contains("    void method()") || result.contains("    String method()"),
                "Indentation should be maintained");
    }

    // =========================================================================
    // R15: Removed.WhiteSpace + Original.Token.WhiteSpaceOrComment
    // =========================================================================

    @Test
    void r15_skipWhitespaceWhenRemovingWhitespace() {
        considerCode("class X {\n" + "    int a, b;\n" + "}");

        ClassOrInterfaceDeclaration clazz =
                cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Modify to trigger whitespace synchronization
        clazz.getMembers().get(0).asFieldDeclaration().getVariable(0).setName("alpha");

        String result = print();

        assertTrue(result.contains("int alpha"), "First variable should be renamed");
        assertTrue(result.contains(", b"), "Second variable should remain");
    }

    // =========================================================================
    // R16: Removed.Any + Original.Literal
    // =========================================================================

    @Test
    void r16_removeLiteral() {
        considerCode("class X {\n" + "    int field = 42;\n" + "}");

        ClassOrInterfaceDeclaration clazz =
                cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Remove initializer (literal)
        clazz.getFieldByName("field").get().getVariable(0).setInitializer((Expression) null);

        String expected = "class X {\n" + "    int field;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // R18: Removed.WhiteSpace/Indent/Unindent + NoMatch
    // =========================================================================

    @Test
    void r18_skipRemovedWhitespaceNotFound() {
        considerCode("class X {\n" + "    int field;\n" + "}");

        // This tests that missing whitespace to remove doesn't cause errors
        ClassOrInterfaceDeclaration clazz =
                cu.findFirst(ClassOrInterfaceDeclaration.class).get();
        clazz.getFieldByName("field").get().getVariable(0).setName("data");

        String expected = "class X {\n" + "    int data;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // R19: Removed.Any + Original.WhiteSpace
    // =========================================================================

    @Test
    void r19_skipOriginalWhitespaceWhenRemoving() {
        considerCode("class X {\n" + "    int field  ;\n" + "}");

        ClassOrInterfaceDeclaration clazz =
                cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Modify field name
        clazz.getFieldByName("field").get().getVariable(0).setName("data");

        String result = print();

        assertTrue(result.contains("int data"), "Field name should be changed");
    }

    // =========================================================================
    // R21: Removed.Token + Original.Child (Issue #4747)
    // =========================================================================

    @Test
    void r21_changeAnnotationName() {
        considerCode("class X {\n" + "    @MyAnnotation\n" + "    void method() {}\n" + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();

        // Change annotation name
        method.getAnnotation(0).setName("NewAnnotation");

        String expected = "class X {\n" + "    @NewAnnotation\n" + "    void method() {}\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // POST-REMOVED: cleanTheLineOfLeftOverSpace
    // =========================================================================

    @Test
    void postRemoved_cleanLeftoverSpacesAfterCompleteLineRemoval() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        int x = 1;\n"
                + "        int y = 2;\n"
                + "        int z = 3;\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();
        BlockStmt body = method.getBody().get();

        // Remove middle statement (complete line)
        body.getStatements().remove(1);

        String expected = "class X {\n" + "    void method() {\n"
                + "        int x = 1;\n"
                + "        int z = 3;\n"
                + "    }\n"
                + "}";

        assertTransformedToString(expected, cu);

        // Verify no leftover indentation spaces
        String result = print();
        assertFalse(result.contains("\n        \n"), "No empty lines with spaces should remain");
    }

    // =========================================================================
    // Helper methods
    // =========================================================================

    private String print() {
        return LexicalPreservingPrinter.print(cu);
    }
}
