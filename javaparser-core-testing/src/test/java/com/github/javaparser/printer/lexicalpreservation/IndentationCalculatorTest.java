/*
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

import com.github.javaparser.GeneratedJavaParserConstants;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

class IndentationCalculatorTest {

    // Helper methods to create tokens
    private TokenTextElement newline() {
        return new TokenTextElement(GeneratedJavaParserConstants.UNIX_EOL, "\n");
    }

    private TokenTextElement space() {
        return new TokenTextElement(GeneratedJavaParserConstants.SPACE, " ");
    }

    private TokenTextElement tab() {
        return new TokenTextElement(GeneratedJavaParserConstants.SPACE, "\t");
    }

    private TokenTextElement token(int kind, String text) {
        return new TokenTextElement(kind, text);
    }

    @Nested
    @DisplayName("computeFromPrecedingElements tests")
    class ComputeFromPrecedingElementsTests {

        @Test
        @DisplayName("Should compute indentation after newline")
        void computeAfterNewline() {
            List<TextElement> elements = Arrays.asList(
                    token(GeneratedJavaParserConstants.PUBLIC, "public"),
                    newline(),
                    space(),
                    space(),
                    space(),
                    space());

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            assertEquals(4, indentation.size());
            assertTrue(indentation.stream().allMatch(e -> e.isSpaceOrTab()));
        }

        @Test
        @DisplayName("Should return empty when no newline found")
        void noNewline() {
            List<TextElement> elements =
                    Arrays.asList(space(), space(), token(GeneratedJavaParserConstants.PUBLIC, "public"));

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            assertTrue(indentation.isEmpty());
        }

        @Test
        @DisplayName("Should stop at first non-whitespace after newline")
        void stopAtNonWhitespace() {
            List<TextElement> elements =
                    Arrays.asList(newline(), space(), space(), token(GeneratedJavaParserConstants.PUBLIC, "public"));

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            assertEquals(2, indentation.size());
        }

        @Test
        @DisplayName("Should handle multiple newlines and use last one")
        void multipleNewlines() {
            List<TextElement> elements =
                    Arrays.asList(newline(), space(), space(), newline(), space(), space(), space(), space());

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            // Should use indentation after the LAST newline (index 3)
            assertEquals(4, indentation.size());
        }

        @Test
        @DisplayName("Should handle empty list")
        void emptyList() {
            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(Collections.emptyList());

            assertTrue(indentation.isEmpty());
        }

        @Test
        @DisplayName("Should handle only newline")
        void onlyNewline() {
            List<TextElement> elements = Arrays.asList(newline());

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            assertTrue(indentation.isEmpty());
        }

        @Test
        @DisplayName("Should handle newline at end with no trailing spaces")
        void newlineAtEnd() {
            List<TextElement> elements = Arrays.asList(token(GeneratedJavaParserConstants.PUBLIC, "public"), newline());

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            assertTrue(indentation.isEmpty());
        }

        @Test
        @DisplayName("Should handle consecutive newlines")
        void consecutiveNewlines() {
            List<TextElement> elements = Arrays.asList(newline(), newline(), space(), space());

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            // Should get indentation after last newline
            assertEquals(2, indentation.size());
        }

        @Test
        @DisplayName("Should handle mixed tabs and spaces")
        void mixedTabsAndSpaces() {
            List<TextElement> elements = Arrays.asList(newline(), tab(), space(), tab(), space());

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            assertEquals(4, indentation.size());
            assertTrue(indentation.stream().allMatch(e -> e.isSpaceOrTab()));
        }

        @Test
        @DisplayName("Should not modify input list")
        void doesNotModifyInput() {
            List<TextElement> original = new ArrayList<>(Arrays.asList(newline(), space(), space()));
            int originalSize = original.size();

            IndentationCalculator.computeFromPrecedingElements(original);

            assertEquals(originalSize, original.size());
        }
    }

    @Nested
    @DisplayName("extractIndentationFromTokens tests")
    class ExtractIndentationFromTokensTests {

        @Test
        @DisplayName("Should extract leading whitespace")
        void extractLeadingWhitespace() {
            List<TextElement> tokens = Arrays.asList(
                    space(), space(), space(), space(), token(GeneratedJavaParserConstants.PUBLIC, "public"));

            List<TextElement> indentation = IndentationCalculator.extractIndentationFromTokens(tokens);

            assertEquals(4, indentation.size());
        }

        @Test
        @DisplayName("Should return empty when no leading whitespace")
        void noLeadingWhitespace() {
            List<TextElement> tokens = Arrays.asList(token(GeneratedJavaParserConstants.PUBLIC, "public"), space());

            List<TextElement> indentation = IndentationCalculator.extractIndentationFromTokens(tokens);

            assertTrue(indentation.isEmpty());
        }

        @Test
        @DisplayName("Should extract all spaces if list only contains whitespace")
        void onlyWhitespace() {
            List<TextElement> tokens = Arrays.asList(space(), space(), space());

            List<TextElement> indentation = IndentationCalculator.extractIndentationFromTokens(tokens);

            assertEquals(3, indentation.size());
        }

        @Test
        @DisplayName("Should handle empty list")
        void emptyList() {
            List<TextElement> indentation = IndentationCalculator.extractIndentationFromTokens(Collections.emptyList());

            assertTrue(indentation.isEmpty());
        }

        @Test
        @DisplayName("Should handle mixed tabs and spaces")
        void mixedTabsAndSpaces() {
            List<TextElement> tokens =
                    Arrays.asList(tab(), space(), tab(), token(GeneratedJavaParserConstants.PUBLIC, "public"));

            List<TextElement> indentation = IndentationCalculator.extractIndentationFromTokens(tokens);

            assertEquals(3, indentation.size());
        }

        @Test
        @DisplayName("Should stop at newline")
        void stopAtNewline() {
            List<TextElement> tokens = Arrays.asList(space(), space(), newline(), space());

            List<TextElement> indentation = IndentationCalculator.extractIndentationFromTokens(tokens);

            assertEquals(2, indentation.size());
        }

        @Test
        @DisplayName("Should not modify input list")
        void doesNotModifyInput() {
            List<TextElement> original = new ArrayList<>(
                    Arrays.asList(space(), space(), token(GeneratedJavaParserConstants.PUBLIC, "public")));
            int originalSize = original.size();

            IndentationCalculator.extractIndentationFromTokens(original);

            assertEquals(originalSize, original.size());
        }
    }

    @Nested
    @DisplayName("createIndentationBlock tests")
    class CreateIndentationBlockTests {

        @Test
        @DisplayName("Should create block of 4 spaces")
        void createBlock() {
            List<TextElement> block = IndentationCalculator.createIndentationBlock();

            assertEquals(4, block.size());
            assertTrue(block.stream().allMatch(e -> e.isSpaceOrTab()));
        }

        @Test
        @DisplayName("Should create new instance each time")
        void newInstanceEachTime() {
            List<TextElement> block1 = IndentationCalculator.createIndentationBlock();
            List<TextElement> block2 = IndentationCalculator.createIndentationBlock();

            assertNotSame(block1, block2);
            assertEquals(block1.size(), block2.size());
        }

        @Test
        @DisplayName("Should create block with STANDARD_INDENTATION_SIZE elements")
        void usesStandardSize() {
            List<TextElement> block = IndentationCalculator.createIndentationBlock();

            assertEquals(IndentationConstants.STANDARD_INDENTATION_SIZE, block.size());
        }

        @Test
        @DisplayName("Should create mutable list")
        void createsMutableList() {
            List<TextElement> block = IndentationCalculator.createIndentationBlock();

            // Should be able to modify the returned list
            assertDoesNotThrow(() -> block.add(space()));
        }
    }

    @Nested
    @DisplayName("analyzeEnforcingContext tests")
    class AnalyzeEnforcingContextTests {

        @Test
        @DisplayName("Should return no extra characters when index points to non-whitespace")
        void indexOnNonWhitespace() {
            NodeText nodeText = new NodeText();
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public");

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 0);

            assertFalse(ctx.hasExtraCharacters());
            assertEquals(0, ctx.getExtraCharacters());
            assertEquals(0, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should detect extra spaces in a whitespace-only line")
        void whitespaceOnlyLine() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline()); // index 0
            nodeText.addElement(space()); // index 1
            nodeText.addElement(space()); // index 2
            nodeText.addElement(space()); // index 3
            nodeText.addElement(space()); // index 4

            // Analyzing from index 2 (middle of whitespace sequence)
            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 2);

            assertTrue(ctx.hasExtraCharacters());
            // Should count: 1 backward (index 1) + current + 2 forward (indices 3,4) = 4 total
            assertEquals(4, ctx.getExtraCharacters());
            assertEquals(1, ctx.getStartIndex()); // Start of whitespace sequence
        }

        @Test
        @DisplayName("Should return zero when there is non-whitespace before the newline")
        void nonWhitespaceElement() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline()); // index 0
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public"); // index 1
            nodeText.addElement(space()); // index 2

            // Analyzing at the non-whitespace token itself
            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 1);

            assertFalse(ctx.hasExtraCharacters());
            assertEquals(0, ctx.getExtraCharacters());
        }

        @Test
        @DisplayName("Should handle invalid negative index")
        void negativeIndex() {
            NodeText nodeText = new NodeText();
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public");

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, -1);

            assertFalse(ctx.hasExtraCharacters());
            assertEquals(0, ctx.getExtraCharacters());
            assertEquals(-1, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should handle index beyond list size")
        void indexBeyondSize() {
            NodeText nodeText = new NodeText();
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public");

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 10);

            assertFalse(ctx.hasExtraCharacters());
            assertEquals(0, ctx.getExtraCharacters());
            assertEquals(10, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should stop scanning backward at newline")
        void stopAtNewline() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline()); // index 0
            nodeText.addElement(space()); // index 1
            nodeText.addElement(space()); // index 2
            nodeText.addElement(space()); // index 3

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 2);

            assertTrue(ctx.hasExtraCharacters());
            // Counts backward to index 1, current (2), forward to index 3 = 3 total
            assertEquals(3, ctx.getExtraCharacters());
            assertEquals(1, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should count spaces both before and after index")
        void countBeforeAndAfter() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline()); // index 0
            nodeText.addElement(space()); // index 1
            nodeText.addElement(space()); // index 2 ← analyzing here
            nodeText.addElement(space()); // index 3
            nodeText.addElement(space()); // index 4
            nodeText.addElement(space()); // index 5

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 2);

            assertTrue(ctx.hasExtraCharacters());
            // Backward: 1 (index 1), current: 1 (index 2), forward: 3 (indices 3,4,5) = 5 total
            assertEquals(5, ctx.getExtraCharacters());
            assertEquals(1, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should handle analyzing at first space after newline")
        void analyzeAtFirstSpace() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline()); // index 0
            nodeText.addElement(space()); // index 1 ← analyzing here
            nodeText.addElement(space()); // index 2

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 1);

            assertTrue(ctx.hasExtraCharacters());
            // Current (1) + forward (2) = 2 total
            assertEquals(2, ctx.getExtraCharacters());
            assertEquals(1, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should handle analyzing at last space before non-whitespace")
        void analyzeAtLastSpace() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline()); // index 0
            nodeText.addElement(space()); // index 1
            nodeText.addElement(space()); // index 2 ← analyzing here
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public"); // index 3

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 2);

            assertTrue(ctx.hasExtraCharacters());
            // Backward: 1 (index 1), current: 1 (index 2) = 2 total (stops at public)
            assertEquals(2, ctx.getExtraCharacters());
            assertEquals(1, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should return zero for single non-whitespace element")
        void singleNonWhitespace() {
            NodeText nodeText = new NodeText();
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public");

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 0);

            assertFalse(ctx.hasExtraCharacters());
        }

        @Test
        @DisplayName("Should handle empty NodeText")
        void emptyNodeText() {
            NodeText nodeText = new NodeText();

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 0);

            assertFalse(ctx.hasExtraCharacters());
            assertEquals(0, ctx.getExtraCharacters());
            assertEquals(0, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should stop forward scan at newline")
        void stopForwardScanAtNewline() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline()); // index 0
            nodeText.addElement(space()); // index 1 ← analyzing here
            nodeText.addElement(space()); // index 2
            nodeText.addElement(newline()); // index 3
            nodeText.addElement(space()); // index 4 (not counted)

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 1);

            assertTrue(ctx.hasExtraCharacters());
            // Current (1) + forward (2) = 2 total (stops at second newline)
            assertEquals(2, ctx.getExtraCharacters());
            assertEquals(1, ctx.getStartIndex());
        }

        @Test
        @DisplayName("Should handle index at position 0 with whitespace")
        void indexAtZeroWithWhitespace() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(space()); // index 0 ← analyzing here
            nodeText.addElement(space()); // index 1

            // No newline before, and index is 0, so backward scan doesn't run
            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 0);

            assertTrue(ctx.hasExtraCharacters());
            // Only forward scan: current (0) + forward (1) = 2 total
            assertEquals(2, ctx.getExtraCharacters());
            assertEquals(0, ctx.getStartIndex());
        }
    }

    @Nested
    @DisplayName("removeExcessIndentation tests")
    class RemoveExcessIndentationTests {

        @Test
        @DisplayName("Should remove specified number of elements")
        void removeSpecifiedCount() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public");

            int newIndex = IndentationCalculator.removeExcessIndentation(nodeText, 0, 2);

            assertEquals(3, nodeText.numberOfElements()); // 2 spaces removed, 2 spaces + public remain
            assertEquals(0, newIndex);
        }

        @Test
        @DisplayName("Should handle removing more than available")
        void removeMoreThanAvailable() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(space());
            nodeText.addElement(space());

            int newIndex = IndentationCalculator.removeExcessIndentation(nodeText, 0, 10);

            assertEquals(0, nodeText.numberOfElements());
            assertEquals(0, newIndex);
        }

        @Test
        @DisplayName("Should handle removing zero elements")
        void removeZero() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(space());
            nodeText.addElement(space());
            int originalSize = nodeText.numberOfElements();

            int newIndex = IndentationCalculator.removeExcessIndentation(nodeText, 0, 0);

            assertEquals(originalSize, nodeText.numberOfElements());
            assertEquals(0, newIndex);
        }

        @Test
        @DisplayName("Should handle invalid start index")
        void invalidStartIndex() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(space());

            int newIndex = IndentationCalculator.removeExcessIndentation(nodeText, -1, 2);

            assertEquals(1, nodeText.numberOfElements()); // Nothing removed
            assertEquals(-1, newIndex);
        }

        @Test
        @DisplayName("Should remove from middle of list")
        void removeFromMiddle() {
            NodeText nodeText = new NodeText();
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public");
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());

            int newIndex = IndentationCalculator.removeExcessIndentation(nodeText, 1, 2);

            assertEquals(2, nodeText.numberOfElements()); // public + 1 space
            assertEquals(1, newIndex);
        }
    }

    @Nested
    @DisplayName("enforceIndentation tests")
    class EnforceIndentationTests {

        @Test
        @DisplayName("Should enforce indentation preserving specified characters")
        void enforceWithPreserve() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());

            int newIndex = IndentationCalculator.enforceIndentation(nodeText, 3, 4);

            // Should have removed 2 extra spaces (6 total - 4 to preserve)
            assertEquals(5, nodeText.numberOfElements()); // newline + 4 spaces
            assertEquals(5, newIndex); // 1 (start) + 4 (preserved)
        }

        @Test
        @DisplayName("Should do nothing when no extra characters")
        void noExtraCharactersNoEnforcement() {
            NodeText nodeText = new NodeText();
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public");
            int originalSize = nodeText.numberOfElements();

            int newIndex = IndentationCalculator.enforceIndentation(nodeText, 0, 4);

            assertEquals(originalSize, nodeText.numberOfElements());
            assertEquals(0, newIndex);
        }

        @Test
        @DisplayName("Should preserve all characters when preserve count equals extra")
        void preserveEqualsExtra() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());

            int newIndex = IndentationCalculator.enforceIndentation(nodeText, 2, 4);

            // Should not remove anything (4 spaces, preserve 4)
            assertEquals(5, nodeText.numberOfElements()); // newline + 4 spaces
            assertEquals(1, newIndex); // Start of the space sequence
        }

        @Test
        @DisplayName("Should remove all extra when preserve is zero")
        void preserveZero() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());

            int newIndex = IndentationCalculator.enforceIndentation(nodeText, 2, 0);

            // Should remove all 4 spaces
            assertEquals(1, nodeText.numberOfElements()); // Only newline
            assertEquals(1, newIndex);
        }

        @Test
        @DisplayName("Should handle preserve count greater than extra")
        void preserveGreaterThanExtra() {
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline());
            nodeText.addElement(space());
            nodeText.addElement(space());

            int newIndex = IndentationCalculator.enforceIndentation(nodeText, 1, 10);

            // Should not remove anything (2 spaces, but want to preserve 10)
            assertEquals(3, nodeText.numberOfElements()); // newline + 2 spaces
            assertEquals(1, newIndex);
        }
    }

    @Nested
    @DisplayName("EnforcingContext tests")
    class EnforcingContextTests {

        @Test
        @DisplayName("Should create context with correct values")
        void createContext() {
            IndentationCalculator.EnforcingContext ctx = new IndentationCalculator.EnforcingContext(5, 10);

            assertEquals(5, ctx.getStartIndex());
            assertEquals(10, ctx.getExtraCharacters());
            assertTrue(ctx.hasExtraCharacters());
        }

        @Test
        @DisplayName("Should report no extra characters when zero")
        void noExtraCharacters() {
            IndentationCalculator.EnforcingContext ctx = new IndentationCalculator.EnforcingContext(0, 0);

            assertFalse(ctx.hasExtraCharacters());
        }

        @Test
        @DisplayName("Should be equal to itself")
        void equalsItself() {
            IndentationCalculator.EnforcingContext ctx = new IndentationCalculator.EnforcingContext(5, 10);

            assertEquals(ctx, ctx);
        }

        @Test
        @DisplayName("Should be equal to context with same values")
        void equalsSameValues() {
            IndentationCalculator.EnforcingContext ctx1 = new IndentationCalculator.EnforcingContext(5, 10);
            IndentationCalculator.EnforcingContext ctx2 = new IndentationCalculator.EnforcingContext(5, 10);

            assertEquals(ctx1, ctx2);
        }

        @Test
        @DisplayName("Should not be equal to context with different values")
        void notEqualsDifferentValues() {
            IndentationCalculator.EnforcingContext ctx1 = new IndentationCalculator.EnforcingContext(5, 10);
            IndentationCalculator.EnforcingContext ctx2 = new IndentationCalculator.EnforcingContext(5, 11);

            assertNotEquals(ctx1, ctx2);
        }

        @Test
        @DisplayName("Should not be equal to null")
        void notEqualsNull() {
            IndentationCalculator.EnforcingContext ctx = new IndentationCalculator.EnforcingContext(5, 10);

            assertNotEquals(ctx, null);
        }

        @Test
        @DisplayName("Should not be equal to different type")
        void notEqualsDifferentType() {
            IndentationCalculator.EnforcingContext ctx = new IndentationCalculator.EnforcingContext(5, 10);

            assertNotEquals(ctx, "not a context");
        }

        @Test
        @DisplayName("Should have same hashCode for equal contexts")
        void hashCodeConsistent() {
            IndentationCalculator.EnforcingContext ctx1 = new IndentationCalculator.EnforcingContext(5, 10);
            IndentationCalculator.EnforcingContext ctx2 = new IndentationCalculator.EnforcingContext(5, 10);

            assertEquals(ctx1.hashCode(), ctx2.hashCode());
        }

        @Test
        @DisplayName("Should have valid toString")
        void toStringValid() {
            IndentationCalculator.EnforcingContext ctx = new IndentationCalculator.EnforcingContext(5, 10);

            String str = ctx.toString();

            assertNotNull(str);
            assertTrue(str.contains("5"));
            assertTrue(str.contains("10"));
        }
    }

    @Nested
    @DisplayName("Edge cases and integration")
    class EdgeCasesTests {

        @Test
        @DisplayName("Should handle complex scenario with multiple operations")
        void complexScenario() {
            // Create a NodeText with newline and various indentation
            NodeText nodeText = new NodeText();
            nodeText.addElement(newline());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addElement(space());
            nodeText.addToken(GeneratedJavaParserConstants.PUBLIC, "public");

            // Analyze
            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 4);
            assertTrue(ctx.hasExtraCharacters());

            // Enforce keeping only 4 spaces
            int newIndex = IndentationCalculator.enforceIndentation(nodeText, 4, 4);

            assertEquals(6, nodeText.numberOfElements()); // newline + 4 spaces + public
            assertEquals(5, newIndex);
        }

        @Test
        @DisplayName("Should handle empty NodeText")
        void emptyNodeText() {
            NodeText nodeText = new NodeText();

            IndentationCalculator.EnforcingContext ctx = IndentationCalculator.analyzeEnforcingContext(nodeText, 0);

            assertFalse(ctx.hasExtraCharacters());
        }

        @Test
        @DisplayName("Should work with tabs")
        void workWithTabs() {
            List<TextElement> elements = Arrays.asList(newline(), tab(), tab());

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            assertEquals(2, indentation.size());
            assertTrue(indentation.stream().allMatch(e -> e.isSpaceOrTab()));
        }

        @Test
        @DisplayName("Should handle very large indentation")
        void veryLargeIndentation() {
            List<TextElement> elements = new ArrayList<>();
            elements.add(newline());
            for (int i = 0; i < 1000; i++) {
                elements.add(space());
            }

            List<TextElement> indentation = IndentationCalculator.computeFromPrecedingElements(elements);

            assertEquals(1000, indentation.size());
        }
    }
}
