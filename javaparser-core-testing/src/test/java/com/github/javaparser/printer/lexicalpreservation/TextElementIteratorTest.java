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

import static com.github.javaparser.GeneratedJavaParserConstants.SPACE;
import static com.github.javaparser.GeneratedJavaParserConstants.UNIX_EOL;
import static org.junit.jupiter.api.Assertions.*;

import com.github.javaparser.GeneratedJavaParserConstants;
import java.util.NoSuchElementException;
import org.junit.jupiter.api.Test;

class TextElementIteratorTest {

    private static TokenTextElement space() {
        return new TokenTextElement(SPACE, " ");
    }

    private static TokenTextElement newline() {
        return new TokenTextElement(UNIX_EOL, "\n");
    }

    private static TokenTextElement tab() {
        return new TokenTextElement(SPACE, "\t");
    }

    // === CONSTRUCTION TESTS ===

    @Test
    void constructor_withValidIndex_createsIterator() {
        TextElementList list = TextElementList.of(space(), newline(), tab());

        TextElementIterator iterator = list.iterator(1);

        assertEquals(-1, iterator.currentIndex());
    }

    @Test
    void constructor_withZeroIndex_startsAtBeginning() {
        TextElementList list = TextElementList.of(space(), newline());

        TextElementIterator iterator = list.iterator(0);

        assertEquals(-1, iterator.currentIndex());
    }

    @Test
    void constructor_withInvalidIndex_throwsIndexOutOfBoundsException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(IndexOutOfBoundsException.class, () -> list.iterator(-1));
        assertThrows(IndexOutOfBoundsException.class, () -> list.iterator(10));
    }

    // === CURRENT INDEX TESTS ===

    @Test
    void currentIndex_returnsInitialIndex() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator(1);

        assertEquals(-1, iterator.currentIndex());
    }

    @Test
    void currentIndex_updatesAfterNext() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator(0);

        iterator.next();

        assertEquals(0, iterator.currentIndex());
    }

    @Test
    void currentIndex_updatesAfterPrevious() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator(2);

        iterator.previous();

        assertEquals(1, iterator.currentIndex());
    }

    @Test
    void currentIndex_matchesNextIndex() {
        TextElementList list = TextElementList.of(space(), newline());
        TextElementIterator iterator = list.iterator(0);

        assertEquals(-1, iterator.currentIndex());
        assertEquals(0, iterator.nextIndex());
    }

    // === HAS NEXT TESTS ===

    @Test
    void hasNext_returnsTrueWhenElementsRemain() {
        TextElementList list = TextElementList.of(space(), newline());
        TextElementIterator iterator = list.iterator(0);

        assertTrue(iterator.hasNext());
    }

    @Test
    void hasNext_returnsFalseAtEnd() {
        TextElementList list = TextElementList.of(space());
        TextElementIterator iterator = list.iterator(0);

        iterator.next();

        assertFalse(iterator.hasNext());
    }

    // === NEXT TESTS ===

    @Test
    void next_returnsCurrentElementAndAdvances() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator(0);

        TextElement first = iterator.next();
        TextElement second = iterator.next();

        assertTrue(first.isSpaceOrTab());
        assertTrue(second.isNewline());
        assertEquals(1, iterator.currentIndex());
    }

    @Test
    void next_atEnd_throwsNoSuchElementException() {
        TextElementList list = TextElementList.of(space());
        TextElementIterator iterator = list.iterator(0);

        iterator.next();

        assertThrows(NoSuchElementException.class, iterator::next);
    }

    // === HAS PREVIOUS TESTS ===

    @Test
    void hasPrevious_returnsTrueWhenNotAtStart() {
        TextElementList list = TextElementList.of(space(), newline());
        TextElementIterator iterator = list.iterator(1);

        assertTrue(iterator.hasPrevious());
    }

    @Test
    void hasPrevious_returnsFalseAtStart() {
        TextElementList list = TextElementList.of(space());
        TextElementIterator iterator = list.iterator(0);

        assertFalse(iterator.hasPrevious());
    }

    // === PREVIOUS TESTS ===

    @Test
    void previous_returnsPreviousElementAndRetracts() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator(2);

        TextElement first = iterator.previous();
        TextElement second = iterator.previous();

        assertTrue(first.isNewline()); // iterator(2).previous() returns element at index 1
        assertTrue(second.isSpaceOrTab()); // After first previous(), iterator(1).previous() returns element at index 0
        assertEquals(0, iterator.currentIndex());
    }

    @Test
    void previous_atStart_throwsNoSuchElementException() {
        TextElementList list = TextElementList.of(space());
        TextElementIterator iterator = list.iterator(0);

        assertThrows(NoSuchElementException.class, iterator::previous);
    }

    // === NEXT INDEX TESTS ===

    @Test
    void nextIndex_returnsIndexOfNextElement() {
        TextElementList list = TextElementList.of(space(), newline());
        TextElementIterator iterator = list.iterator(0);

        assertEquals(0, iterator.nextIndex());
        iterator.next();
        assertEquals(1, iterator.nextIndex());
    }

    // === PREVIOUS INDEX TESTS ===

    @Test
    void previousIndex_returnsIndexOfPreviousElement() {
        TextElementList list = TextElementList.of(space(), newline());
        TextElementIterator iterator = list.iterator(1);

        assertEquals(0, iterator.previousIndex());
    }

    @Test
    void previousIndex_atStart_returnsMinusOne() {
        TextElementList list = TextElementList.of(space());
        TextElementIterator iterator = list.iterator(0);

        assertEquals(-1, iterator.previousIndex());
    }

    // === REMOVE TESTS ===

    @Test
    void remove_removesLastReturnedElement() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator(0);

        iterator.next();
        iterator.remove();

        assertEquals(2, list.size());
        assertTrue(list.get(0).isNewline());
    }

    @Test
    void remove_withoutNext_throwsIllegalStateException() {
        TextElementList list = TextElementList.of(space());
        TextElementIterator iterator = list.iterator(0);

        assertThrows(IllegalStateException.class, iterator::remove);
    }

    // === SET TESTS ===

    @Test
    void set_replacesLastReturnedElement() {
        TextElementList list = TextElementList.of(space(), newline());
        TextElementIterator iterator = list.iterator(0);
        TokenTextElement replacement = tab();

        iterator.next();
        iterator.set(replacement);

        assertEquals(replacement, list.get(0));
    }

    @Test
    void set_withoutNext_throwsIllegalStateException() {
        TextElementList list = TextElementList.of(space());
        TextElementIterator iterator = list.iterator(0);

        assertThrows(IllegalStateException.class, () -> iterator.set(newline()));
    }

    // === ADD TESTS ===

    @Test
    void add_insertsElementBeforeCurrent() {
        TextElementList list = TextElementList.of(space(), tab());
        TextElementIterator iterator = list.iterator(1);

        iterator.add(newline());

        assertEquals(3, list.size());
        assertTrue(list.get(1).isNewline());
        assertEquals(1, iterator.currentIndex()); // Advanced after add
    }

    // === BIDIRECTIONAL ITERATION TESTS ===

    @Test
    void bidirectionalIteration_worksCorrectly() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator(1);
        iterator.next(); // read element 1, currentIndex = 1
        iterator.previous(); // read element 1, currentIndex = 1
        assertEquals(1, iterator.currentIndex());
    }

    // === FULL ITERATION TEST ===

    @Test
    void fullIteration_processesAllElements() {
        TextElementList list = TextElementList.of(space(), newline(), tab(), space());
        TextElementIterator iterator = list.iterator(0);

        int count = 0;
        while (iterator.hasNext()) {
            iterator.next();
            count++;
        }

        assertEquals(4, count);
        assertEquals(3, iterator.currentIndex());
    }

    // === USAGE PATTERN TEST (replaces ArrayIterator) ===

    @Test
    void usagePattern_searchingForComments() {
        // Simulates Difference.posOfNextComment() usage pattern
        TextElementList list = TextElementList.of(
                space(), space(), new TokenTextElement(GeneratedJavaParserConstants.SINGLE_LINE_COMMENT, "// comment"));
        TextElementIterator iterator = list.iterator(0);

        int commentIndex = -1;
        while (iterator.hasNext()) {
            TextElement element = iterator.next();
            if (!element.isSpaceOrTab()) {
                commentIndex = iterator.currentIndex();
                break;
            }
        }

        assertEquals(2, commentIndex);
    }
}
