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

import static com.github.javaparser.printer.lexicalpreservation.IndentationConstants.STANDARD_INDENTATION_SIZE;

import com.github.javaparser.GeneratedJavaParserConstants;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Provides stateless utility methods for indentation calculations and analysis.
 *
 * This class contains pure functions that compute indentation-related values
 * without maintaining any state. All methods are static and can be used
 * independently without creating an instance.
 *
 * Typical operations include:
 * - Computing indentation from preceding elements
 * - Analyzing indentation context for enforcement
 * - Creating standard indentation blocks
 * - Extracting indentation from token sequences
 *
 * @see IndentationContext for stateful indentation management
 */
public final class IndentationCalculator {

    /**
     * Private constructor to prevent instantiation.
     * This is a utility class with only static methods.
     */
    private IndentationCalculator() {
        throw new AssertionError("IndentationCalculator is a utility class and should not be instantiated");
    }

    /**
     * Computes the indentation that should be used based on the elements preceding
     * the current position. This analyzes the elements to find the last newline
     * and extracts all whitespace characters that follow it.
     *
     * This method is used when we need to match existing indentation in the source code.
     *
     * @param precedingElements elements before the current position
     * @return list of indentation elements (spaces/tabs) after the last newline, or empty list if no newline found
     */
    public static List<TextElement> computeFromPrecedingElements(List<TextElement> precedingElements) {
        int eolIndex = findLastNewlineIndex(precedingElements);
        // No newline found, return empty indentation
        if (eolIndex < 0) {
            return Collections.emptyList();
        }
        // Extract whitespace elements after the newline
        List<TextElement> result = new ArrayList<>();
        for (int i = eolIndex + 1; i < precedingElements.size(); i++) {
            TextElement element = precedingElements.get(i);
            if (element.isSpaceOrTab()) {
                result.add(element);
            } else {
                // Stop at first non-whitespace
                break;
            }
        }
        return result;
    }

    /**
     * Extracts the indentation portion from a list of elements.
     *
     * This method differs from computeFromPrecedingElements because it doesn't look for
     * a newline first - it assumes the list represents tokens after a newline and simply
     * extracts all leading whitespace.
     *
     * This is useful when we have already collected preceding tokens and want to
     * extract just the indentation part.
     *
     * @param precedingTokens tokens that precede the position
     * @return list of indentation elements (leading whitespace only)
     */
    public static List<TextElement> extractIndentationFromTokens(List<TextElement> precedingTokens) {
        List<TextElement> indentation = new ArrayList<>();
        for (TextElement element : precedingTokens) {
            if (element.isSpaceOrTab()) {
                indentation.add(element);
            } else {
                // Stop at first non-whitespace
                break;
            }
        }
        return indentation;
    }

    /**
     * Creates a single indentation block of STANDARD_INDENTATION_SIZE spaces.
     * This is used when we need to add one level of indentation temporarily.
     *
     * @return list containing STANDARD_INDENTATION_SIZE space elements
     */
    public static List<TextElement> createIndentationBlock() {
        List<TextElement> block = new ArrayList<>(STANDARD_INDENTATION_SIZE);
        for (int i = 0; i < STANDARD_INDENTATION_SIZE; i++) {
            block.add(new TokenTextElement(GeneratedJavaParserConstants.SPACE, " "));
        }
        return block;
    }

    /**
     * Analyzes the indentation enforcement context at a given position in the node text.
     *
     * <p><b>Context and Purpose:</b></p>
     * This method is primarily used by the {@link Difference} class during AST modification
     * to determine if excess whitespace should be removed after deleting elements. When a node
     * is removed from the AST, surrounding whitespace may need to be adjusted to maintain
     * proper formatting.
     *
     * <p><b>Algorithm Overview:</b></p>
     * The algorithm performs a two-phase scan to identify excess whitespace:
     * <ol>
     *   <li><b>Backward Scan:</b> Looks backward from the given index to find contiguous
     *       whitespace characters, stopping at either a newline or a non-whitespace element.</li>
     *   <li><b>Forward Scan:</b> If the current position contains whitespace, scans forward
     *       to count additional contiguous whitespace characters.</li>
     * </ol>
     *
     * <p><b>Examples:</b></p>
     * <pre>
     * Example 1 - Whitespace between elements after deletion:
     *   Before: "public class A { int foo; }"
     *   After deletion of "int foo;": "public class A { [space][space] }"
     *   analyzeEnforcingContext(nodeText, firstSpaceIndex) returns:
     *     - startIndex: index of first space
     *     - extraCharacters: 2 (both spaces should be considered for removal)
     *
     * Example 2 - Indentation after newline:
     *   Structure: "[newline][space][space][space][space]public"
     *   analyzeEnforcingContext(nodeText, middleSpaceIndex) returns:
     *     - startIndex: index of first space after newline
     *     - extraCharacters: 4 (all indentation spaces)
     *
     * Example 3 - Non-whitespace interrupts sequence:
     *   Structure: "public[space][space]"
     *   analyzeEnforcingContext(nodeText, firstSpaceIndex) returns:
     *     - startIndex: index of first space (reset due to "public")
     *     - extraCharacters: 2 (spaces after "public")
     * </pre>
     *
     * <p><b>Important Behavior:</b></p>
     * When a non-whitespace element is encountered during the backward scan, the context
     * is reset (start becomes the current index, extraCharacters becomes 0), but the forward
     * scan still executes if the current position is whitespace. This allows the method to
     * identify and count trailing spaces after non-whitespace elements.
     *
     * @param nodeText the node text being modified
     * @param index position to analyze (typically points to a position after a deletion)
     * @return context containing the start index and count of excess whitespace characters
     */
    public static EnforcingContext analyzeEnforcingContext(NodeText nodeText, int index) {
        // Guard against invalid indices
        if (index < 0 || index >= nodeText.numberOfElements()) {
            return new EnforcingContext(index, 0);
        }
        // Starting position of whitespace sequence to potentially remove
        int start = index;
        // Total count of excess whitespace characters
        int extraCharacters = 0;
        // ========== PHASE 1: BACKWARD SCAN ==========
        // Scan backward from the position to identify preceding whitespace.
        // This determines if we're at the beginning of a line (after newline) or
        // if there are spaces that should be counted as part of the enforcement context.
        if (index < nodeText.numberOfElements() && index > 0) {
            for (int i = index - 1; i >= 0; i--) {
                // Stop at newline - we've found the line boundary
                if (nodeText.getTextElement(i).isNewline()) {
                    break;
                }
                // If we encounter a non-whitespace element:
                // Reset the context because we're not at the beginning of a line.
                // However, we still need to scan forward to count any trailing spaces.
                if (!nodeText.getTextElement(i).isSpaceOrTab()) {
                    // Reset: we'll only count forward from current position
                    start = index;
                    extraCharacters = 0;
                    break;
                }
                // Found whitespace - expand the sequence backward
                // Update start to this earlier position
                start = i;
                // Count this whitespace character
                extraCharacters++;
            }
        }
        // ========== PHASE 2: FORWARD SCAN ==========
        // Scan forward from the current position to count additional whitespace.
        // This phase ALWAYS executes if the current position is whitespace,
        // even if we reset the context during the backward scan.
        //
        // Example scenario where this matters:
        //   "public[space][space]" - backward scan finds "public" and resets,
        //   but we still need to count the 2 trailing spaces.
        if (index < nodeText.numberOfElements()
                && nodeText.getTextElement(index).isSpaceOrTab()) {
            for (int i = index; i < nodeText.numberOfElements(); i++) {
                // Stop at newline - end of current line
                if (nodeText.getTextElement(i).isNewline()) {
                    break;
                }
                // Stop at non-whitespace - end of whitespace sequence
                if (!nodeText.getTextElement(i).isSpaceOrTab()) {
                    break;
                }
                // Count this whitespace character
                extraCharacters++;
            }
        }
        return new EnforcingContext(start, extraCharacters);
    }

    /**
     * Removes excess indentation characters from the node text.
     *
     * This method modifies the provided NodeText by removing a specified number
     * of elements starting from the given index.
     *
     * @param nodeText the node text to modify
     * @param startIndex where to start removing
     * @param count how many characters to remove
     * @return the new index position after removal
     */
    public static int removeExcessIndentation(NodeText nodeText, int startIndex, int count) {
        int removed = 0;
        while (startIndex >= 0 && startIndex < nodeText.numberOfElements() && removed < count) {
            nodeText.removeElement(startIndex);
            removed++;
        }
        return startIndex;
    }

    /**
     * Applies indentation enforcement at the specified position, preserving
     * the specified number of characters.
     *
     * This is the main enforcement method that:
     * 1. Analyzes the context to determine extra whitespace
     * 2. Calculates how much to remove based on charactersToPreserve
     * 3. Removes the excess
     * 4. Returns the adjusted index
     *
     * @param nodeText the node text to modify
     * @param index current position
     * @param charactersToPreserve how many indentation characters to keep
     * @return the new index position after enforcement
     */
    public static int enforceIndentation(NodeText nodeText, int index, int charactersToPreserve) {
        EnforcingContext ctx = analyzeEnforcingContext(nodeText, index);
        if (!ctx.hasExtraCharacters()) {
            return index;
        }
        int toRemove =
                ctx.getExtraCharacters() > charactersToPreserve ? ctx.getExtraCharacters() - charactersToPreserve : 0;
        int newIndex = removeExcessIndentation(nodeText, ctx.getStartIndex(), toRemove);
        // Adjust for preserved characters
        return toRemove > 0 ? newIndex + charactersToPreserve : newIndex;
    }

    /**
     * Finds the index of the last newline element in the list.
     *
     * @param elements list to search
     * @return index of last newline, or -1 if not found
     */
    private static int findLastNewlineIndex(List<TextElement> elements) {
        for (int i = elements.size() - 1; i >= 0; i--) {
            if (elements.get(i).isNewline()) {
                return i;
            }
        }
        return -1;
    }

    /**
     * Context information for enforcing indentation.
     * Contains the starting position and the number of extra characters to remove.
     *
     * This is an immutable value object returned by analyzeEnforcingContext.
     */
    public static class EnforcingContext {

        private final int startIndex;

        private final int extraCharacters;

        public EnforcingContext(int startIndex, int extraCharacters) {
            this.startIndex = startIndex;
            this.extraCharacters = extraCharacters;
        }

        /**
         * Returns the starting index of the whitespace sequence to potentially remove.
         *
         * @return the start index
         */
        public int getStartIndex() {
            return startIndex;
        }

        /**
         * Returns the total number of extra whitespace characters found.
         *
         * @return count of extra characters
         */
        public int getExtraCharacters() {
            return extraCharacters;
        }

        /**
         * Returns whether there are any extra characters to remove.
         *
         * @return true if extraCharacters > 0
         */
        public boolean hasExtraCharacters() {
            return extraCharacters > 0;
        }

        @Override
        public String toString() {
            return "EnforcingContext{startIndex=" + startIndex + ", extraCharacters=" + extraCharacters + "}";
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            EnforcingContext that = (EnforcingContext) o;
            return startIndex == that.startIndex && extraCharacters == that.extraCharacters;
        }

        @Override
        public int hashCode() {
            return 31 * startIndex + extraCharacters;
        }
    }
}
