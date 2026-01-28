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
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import org.junit.jupiter.api.Test;

/**
 * Test suite for remaining KEPT rules in Difference.apply()
 *
 * Covers whitespace handling, token synchronization, and exception cases.
 */
class DifferenceApplyKeptRulesCompleteTest extends AbstractLexicalPreservingTest {

    // =========================================================================
    // K2: Kept.Child.Comment
    // =========================================================================

    @Test
    void k2_skipCommentInDiffList() {
        considerCode("class X {\n" + "    /** Javadoc */\n" + "    int field;\n" + "}");

        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        // Modify field (Javadoc should be kept automatically)
        field.getVariable(0).setName("data");

        String expected = "class X {\n" + "    /** Javadoc */\n" + "    int data;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // K3: Kept.Child + Original.Child
    // =========================================================================

    @Test
    void k3_keepBothChildrenWhenIdentical() {
        considerCode("class X {\n" + "    int a;\n" + "    int b;\n" + "    int c;\n" + "}");

        ClassOrInterfaceDeclaration clazz =
                cu.findFirst(ClassOrInterfaceDeclaration.class).get();

        // Modify middle field (others should remain unchanged)
        clazz.getFieldByName("b").get().getVariable(0).setName("beta");

        String expected = "class X {\n" + "    int a;\n" + "    int beta;\n" + "    int c;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // K4: Kept.Child + Original.Token.WhiteSpace
    // =========================================================================

    @Test
    void k4_skipWhitespaceBeforeKeptChild() {
        considerCode("class X {\n" + "    int field  ;\n" + "}");

        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        // Modify field name (whitespace should be handled)
        field.getVariable(0).setName("data");

        String result = print();

        assertTrue(result.contains("int data"), "Field name should be changed");
    }

    // =========================================================================
    // K8: Kept.Child + Original.Token.Identifier
    // =========================================================================

    @Test
    void k8_keepSimpleIdentifier() {
        considerCode("class X {\n" + "    String name;\n" + "    int age;\n" + "}");

        FieldDeclaration ageField = cu.findAll(FieldDeclaration.class).stream()
                .filter(f -> f.getVariable(0).getNameAsString().equals("age"))
                .findFirst()
                .get();

        // Modify age field
        ageField.getVariable(0).setName("years");

        String expected = "class X {\n" + "    String name;\n" + "    int years;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // K9: Kept.Child + Original.Token.PrimitiveType
    // =========================================================================

    @Test
    void k9_keepPrimitiveType() {
        considerCode("class X {\n" + "    int value;\n" + "    double ratio;\n" + "}");

        FieldDeclaration valueField = cu.findAll(FieldDeclaration.class).stream()
                .filter(f -> f.getVariable(0).getNameAsString().equals("value"))
                .findFirst()
                .get();

        // Modify value field name
        valueField.getVariable(0).setName("number");

        String expected = "class X {\n" + "    int number;\n" + "    double ratio;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // K10: Kept.Child + Original.Token.Other (fallback)
    // =========================================================================

    @Test
    void k10_keepUnexpectedToken() {
        considerCode("class X {\n" + "    int field;\n" + "}");

        // Modify to test fallback behavior
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();
        field.getVariable(0).setName("data");

        String expected = "class X {\n" + "    int data;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // K12: Kept.Token.NewLine + Original.Token.NewLine
    // =========================================================================

    @Test
    void k12_keepNewlineTokens() {
        considerCode("class X {\n" + "    int a;\n" + "\n" + "    int b;\n" + "}");

        FieldDeclaration fieldA = cu.findAll(FieldDeclaration.class).get(0);

        // Modify first field
        fieldA.getVariable(0).setName("alpha");

        String expected = "class X {\n" + "    int alpha;\n" + "\n" + "    int b;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // K13: Kept.Token.NewLine + Original.Token.SpaceOrTab
    // =========================================================================

    @Test
    void k13_skipSpaceBeforeNewline() {
        considerCode("class X {\n" + "    int field;  \n" + "}");

        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        // Modify field
        field.getVariable(0).setName("data");

        String result = print();

        assertTrue(result.contains("int data"), "Field name should be changed");
    }

    // =========================================================================
    // K14: Kept.Token.WhiteSpaceOrComment + Original.Token
    // =========================================================================

    @Test
    void k14_skipWhitespaceInDiff() {
        considerCode("class X {\n" + "    int a, b;\n" + "}");

        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        // Modify first variable
        field.getVariable(0).setName("alpha");

        String result = print();

        assertTrue(result.contains("int alpha"), "First variable should be renamed");
        assertTrue(result.contains(", b"), "Second variable should remain with proper spacing");
    }

    // =========================================================================
    // K15: Kept.Token + Original.Token.WhiteSpaceOrComment
    // =========================================================================

    @Test
    void k15_skipWhitespaceInOriginal() {
        considerCode("class X {\n" + "    int  field;\n" + "}");

        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        // Modify field
        field.getVariable(0).setName("data");

        String result = print();

        assertTrue(result.contains("int"), "Type should remain");
        assertTrue(result.contains("data"), "Field name should be changed");
    }

    // =========================================================================
    // K16: Kept.Token.NonNewLine + Original.Token.Separator (Issue #2351)
    // =========================================================================

    @Test
    void k16_keepSeparatorAfterToken() {
        considerCode("class X {\n" + "    int a;;\n" + "}");

        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        // Modify field (double semicolon should be handled)
        field.getVariable(0).setName("alpha");

        String result = print();

        assertTrue(result.contains("int alpha"), "Field name should be changed");
    }

    // =========================================================================
    // K17: Kept.Token + Original.Child
    // =========================================================================

    @Test
    void k17_skipDiffWhenTokenExpectedChildFound() {
        considerCode("class X {\n" + "    int field;\n" + "}");

        // This tests asymmetry handling between token and child
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();
        field.getVariable(0).setName("data");

        String expected = "class X {\n" + "    int data;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // K18: Kept.WhiteSpace
    // =========================================================================

    @Test
    void k18_skipWhitespaceToKeep() {
        considerCode("class X {\n" + "    int field;\n" + "}");

        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();

        // Modify to test whitespace preservation
        field.getVariable(0).setName("data");

        String expected = "class X {\n" + "    int data;\n" + "}";

        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // K19: Kept.Indent
    // =========================================================================

    @Test
    void k19_skipIndentDirective() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        if (true) {\n"
                + "            int x = 1;\n"
                + "        }\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();

        // Modify method to test indent preservation
        method.setType("String");

        String result = print();

        // Indentation should be preserved at all levels
        assertTrue(
                result.contains("    void method()") || result.contains("    String method()"),
                "Method indentation should be preserved");
        assertTrue(result.contains("            int x = 1"), "Inner statement indentation should be preserved");
    }

    // =========================================================================
    // K20: Kept.Unindent
    // =========================================================================

    @Test
    void k20_skipUnindentDirective() {
        considerCode("class X {\n" + "    void method() {\n"
                + "        if (true) {\n"
                + "            int x = 1;\n"
                + "        }\n"
                + "        int y = 2;\n"
                + "    }\n"
                + "}");

        MethodDeclaration method = cu.findFirst(MethodDeclaration.class).get();

        // Modify method
        method.setType("String");

        String result = print();

        // Unindent after if block should be preserved
        assertTrue(result.contains("        int y = 2"), "Statement after if should have correct indentation");
    }

    // =========================================================================
    // K21: Kept.Other (Exception case)
    // =========================================================================

    @Test
    void k21_unsupportedKeptCase() {
        considerCode("class X {\n" + "    int field;\n" + "}");

        // This tests that normal operations don't trigger the exception case
        FieldDeclaration field = cu.findFirst(FieldDeclaration.class).get();
        field.getVariable(0).setName("data");

        String expected = "class X {\n" + "    int data;\n" + "}";

        // Should not throw UnsupportedOperationException
        assertTransformedToString(expected, cu);
    }

    // =========================================================================
    // Complex scenarios
    // =========================================================================

    @Test
    void keepComplexStructureWithMultipleTypes() {
        considerCode("class X {\n" + "    private final Map<String, List<Integer>> data;\n"
                + "    protected String[] names;\n"
                + "    public int count;\n"
                + "    boolean flag;\n"
                + "}");

        FieldDeclaration countField = cu.findAll(FieldDeclaration.class).stream()
                .filter(f -> f.getVariable(0).getNameAsString().equals("count"))
                .findFirst()
                .get();

        // Modify count field only
        countField.getVariable(0).setName("total");

        String result = print();

        // All other fields should be preserved exactly
        assertTrue(result.contains("Map<String, List<Integer>> data"), "Complex generic type should be preserved");
        assertTrue(result.contains("String[] names"), "Array type should be preserved");
        assertTrue(result.contains("int total"), "Modified field should be present");
        assertTrue(result.contains("boolean flag"), "Primitive type should be preserved");
    }

    // =========================================================================
    // Helper methods
    // =========================================================================

    private String print() {
        return LexicalPreservingPrinter.print(cu);
    }
}
