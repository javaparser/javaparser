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

import com.github.javaparser.GeneratedJavaParserTokenManager;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Predicate;
import org.junit.jupiter.api.Test;

class TextElementListTest {

    // === FACTORY METHODS ===

    private static TokenTextElement space() {
        return new TokenTextElement(SPACE, " ");
    }

    private static TokenTextElement tab() {
        return new TokenTextElement(SPACE, "\t");
    }

    private static TokenTextElement newline() {
        return new TokenTextElement(UNIX_EOL, "\n");
    }

    private static TokenTextElement token(String text) {
        return new TokenTextElement(GeneratedJavaParserTokenManager.STRING_LITERAL, text);
    }

    // === CONSTRUCTION TESTS ===

    @Test
    void constructor_withNullList_throwsNullPointerException() {
        assertThrows(NullPointerException.class, () -> new TextElementList(null));
    }

    @Test
    void of_createsListWithElements() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        assertEquals(3, list.size());
    }

    @Test
    void empty_createsEmptyList() {
        TextElementList list = TextElementList.empty();
        assertTrue(list.isEmpty());
        assertEquals(0, list.size());
    }

    @Test
    void copyOf_createsIndependentCopy() {
        List<TextElement> original = new ArrayList<>(Arrays.asList(space(), newline()));
        TextElementList list = TextElementList.copyOf(original);

        original.add(tab());

        assertEquals(2, list.size()); // Not affected by original modification
    }

    @Test
    void constructor_wrapsListWithoutCopying() {
        List<TextElement> original = new ArrayList<>(Arrays.asList(space()));
        TextElementList list = new TextElementList(original);

        original.add(newline());

        assertEquals(2, list.size()); // Affected by original modification
    }

    // === FIND FIRST TESTS ===

    @Test
    void findFirst_withMatchingElement_returnsFirstIndex() {
        TextElementList list = TextElementList.of(space(), newline(), space(), newline());

        int index = list.findFirst(TextElement::isNewline);

        assertEquals(1, index);
    }

    @Test
    void findFirst_withNoMatch_returnsMinusOne() {
        TextElementList list = TextElementList.of(space(), tab());

        int index = list.findFirst(TextElement::isNewline);

        assertEquals(-1, index);
    }

    @Test
    void findFirst_onEmptyList_returnsMinusOne() {
        TextElementList list = TextElementList.empty();

        int index = list.findFirst(TextElement::isNewline);

        assertEquals(-1, index);
    }

    @Test
    void findFirst_withNullPredicate_throwsNullPointerException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(NullPointerException.class, () -> list.findFirst(null));
    }

    // === FIND LAST TESTS ===

    @Test
    void findLast_withMatchingElement_returnsLastIndex() {
        TextElementList list = TextElementList.of(space(), newline(), space(), newline());

        int index = list.findLast(TextElement::isNewline);

        assertEquals(3, index);
    }

    @Test
    void findLast_withNoMatch_returnsMinusOne() {
        TextElementList list = TextElementList.of(space(), tab());

        int index = list.findLast(TextElement::isNewline);

        assertEquals(-1, index);
    }

    @Test
    void findLast_onEmptyList_returnsMinusOne() {
        TextElementList list = TextElementList.empty();

        int index = list.findLast(TextElement::isNewline);

        assertEquals(-1, index);
    }

    @Test
    void findLast_withNullPredicate_throwsNullPointerException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(NullPointerException.class, () -> list.findLast(null));
    }

    // === FIND NEXT TESTS ===

    @Test
    void findNext_fromValidIndex_findsNextMatch() {
        TextElementList list = TextElementList.of(newline(), space(), newline(), space());

        int index = list.findNext(1, TextElement::isNewline);

        assertEquals(2, index);
    }

    @Test
    void findNext_fromMatchingIndex_returnsSameIndex() {
        TextElementList list = TextElementList.of(space(), newline(), space());

        int index = list.findNext(1, TextElement::isNewline);

        assertEquals(1, index);
    }

    @Test
    void findNext_withNoMatchAhead_returnsMinusOne() {
        TextElementList list = TextElementList.of(newline(), space(), space());

        int index = list.findNext(1, TextElement::isNewline);

        assertEquals(-1, index);
    }

    @Test
    void findNext_withInvalidFromIndex_returnsMinusOne() {
        TextElementList list = TextElementList.of(space());

        assertEquals(-1, list.findNext(-1, TextElement::isNewline));
        assertEquals(-1, list.findNext(10, TextElement::isNewline));
    }

    @Test
    void findNext_withNullPredicate_throwsNullPointerException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(NullPointerException.class, () -> list.findNext(0, null));
    }

    // === FIND PREVIOUS TESTS ===

    @Test
    void findPrevious_fromValidIndex_findsPreviousMatch() {
        TextElementList list = TextElementList.of(newline(), space(), newline(), space());

        int index = list.findPrevious(2, TextElement::isNewline);

        assertEquals(2, index); // Finds itself first
    }

    @Test
    void findPrevious_searchesBackward() {
        TextElementList list = TextElementList.of(newline(), space(), newline(), space());

        int index = list.findPrevious(1, TextElement::isNewline);

        assertEquals(0, index);
    }

    @Test
    void findPrevious_withNoMatchBehind_returnsMinusOne() {
        TextElementList list = TextElementList.of(space(), space(), newline());

        int index = list.findPrevious(1, TextElement::isNewline);

        assertEquals(-1, index);
    }

    @Test
    void findPrevious_withInvalidFromIndex_returnsMinusOne() {
        TextElementList list = TextElementList.of(space());

        assertEquals(-1, list.findPrevious(-1, TextElement::isNewline));
        assertEquals(-1, list.findPrevious(10, TextElement::isNewline));
    }

    @Test
    void findPrevious_withNullPredicate_throwsNullPointerException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(NullPointerException.class, () -> list.findPrevious(0, null));
    }

    // === INDEX OF (ELEMENT) TESTS ===

    @Test
    void indexOf_findsFirstOccurrence() {
        TokenTextElement target = space();
        TextElementList list = TextElementList.of(newline(), target, newline(), target);

        int index = list.indexOf(target);

        assertEquals(1, index);
    }

    @Test
    void indexOf_withNoMatch_returnsMinusOne() {
        TextElementList list = TextElementList.of(space());

        int index = list.indexOf(newline());

        assertEquals(-1, index);
    }

    @Test
    void indexOf_withNull_searchesForNull() {
        List<TextElement> elements = new ArrayList<>();
        elements.add(space());
        elements.add(null);
        TextElementList list = new TextElementList(elements);

        int index = list.indexOf(null);

        assertEquals(1, index);
    }

    // === LAST INDEX OF (ELEMENT) TESTS ===

    @Test
    void lastIndexOf_findsLastOccurrence() {
        TokenTextElement target = space();
        TextElementList list = TextElementList.of(target, newline(), target, newline());

        int index = list.lastIndexOf(target);

        assertEquals(2, index);
    }

    @Test
    void lastIndexOf_withNoMatch_returnsMinusOne() {
        TextElementList list = TextElementList.of(space());

        int index = list.lastIndexOf(newline());

        assertEquals(-1, index);
    }

    // === INDEX OF FROM INDEX TESTS ===

    @Test
    void indexOfFromIndex_findsNextOccurrence() {
        TokenTextElement target = newline();
        TextElementList list = TextElementList.of(target, space(), target, space());

        int index = list.indexOf(1, target);

        assertEquals(2, index);
    }

    @Test
    void indexOfFromIndex_includesFromIndex() {
        TokenTextElement target = newline();
        TextElementList list = TextElementList.of(space(), target, space());

        int index = list.indexOf(1, target);

        assertEquals(1, index);
    }

    @Test
    void indexOfFromIndex_withInvalidIndex_returnsMinusOne() {
        TextElementList list = TextElementList.of(space());

        assertEquals(-1, list.indexOf(-1, space()));
        assertEquals(-1, list.indexOf(10, space()));
    }

    // === LAST INDEX OF FROM INDEX TESTS ===

    @Test
    void lastIndexOfFromIndex_findsPreviousOccurrence() {
        TokenTextElement target = newline();
        TextElementList list = TextElementList.of(target, space(), target, space());

        int index = list.lastIndexOf(2, target);

        assertEquals(2, index);
    }

    @Test
    void lastIndexOfFromIndex_searchesBackward() {
        TokenTextElement target = newline();
        TextElementList list = TextElementList.of(target, space(), target, space());

        int index = list.lastIndexOf(1, target);

        assertEquals(0, index);
    }

    @Test
    void lastIndexOfFromIndex_withInvalidIndex_returnsMinusOne() {
        TextElementList list = TextElementList.of(space());

        assertEquals(-1, list.lastIndexOf(-1, space()));
        assertEquals(-1, list.lastIndexOf(10, space()));
    }

    // === TAKE WHILE TESTS ===

    @Test
    void takeWhile_returnsMatchingPrefix() {
        TextElementList list = TextElementList.of(space(), space(), newline(), space());

        List<TextElement> result = list.takeWhile(TextElement::isSpaceOrTab);

        assertEquals(2, result.size());
        assertTrue(result.get(0).isSpaceOrTab());
        assertTrue(result.get(1).isSpaceOrTab());
    }

    @Test
    void takeWhile_stopsAtFirstNonMatch() {
        TextElementList list = TextElementList.of(space(), newline(), space());

        List<TextElement> result = list.takeWhile(TextElement::isSpaceOrTab);

        assertEquals(1, result.size());
    }

    @Test
    void takeWhile_onEmptyList_returnsEmptyList() {
        TextElementList list = TextElementList.empty();

        List<TextElement> result = list.takeWhile(TextElement::isSpaceOrTab);

        assertTrue(result.isEmpty());
    }

    @Test
    void takeWhile_withNullPredicate_throwsNullPointerException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(NullPointerException.class, () -> list.takeWhile(null));
    }

    // === SUBLIST TESTS ===

    @Test
    void subList_returnsCorrectRange() {
        TextElementList list = TextElementList.of(space(), newline(), tab(), space());

        List<TextElement> sublist = list.subList(1, 3);

        assertEquals(2, sublist.size());
        assertTrue(sublist.get(0).isNewline());
        assertTrue(sublist.get(1).isSpaceOrTab());
    }

    @Test
    void subList_isBackedByOriginal() {
        List<TextElement> original = new ArrayList<>(Arrays.asList(space(), newline(), tab()));
        TextElementList list = new TextElementList(original);

        List<TextElement> sublist = list.subList(0, 2);
        sublist.clear();

        assertEquals(1, list.size()); // Original affected
    }

    // === INSERT TESTS ===

    @Test
    void insert_addsElementAtIndex() {
        TextElementList list = TextElementList.of(space(), tab());

        list.insert(1, newline());

        assertEquals(3, list.size());
        assertTrue(list.get(1).isNewline());
    }

    @Test
    void insert_withNullElement_throwsNullPointerException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(NullPointerException.class, () -> list.insert(0, null));
    }

    @Test
    void insert_withInvalidIndex_throwsIndexOutOfBoundsException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(IndexOutOfBoundsException.class, () -> list.insert(-1, newline()));
        assertThrows(IndexOutOfBoundsException.class, () -> list.insert(10, newline()));
    }

    // === INSERT ALL TESTS ===

    @Test
    void insertAll_addsAllElements() {
        TextElementList list = TextElementList.of(space(), tab());
        List<TextElement> toInsert = Arrays.asList(newline(), newline());

        list.insertAll(1, toInsert);

        assertEquals(4, list.size());
        assertTrue(list.get(1).isNewline());
        assertTrue(list.get(2).isNewline());
    }

    @Test
    void insertAll_withNullList_throwsNullPointerException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(NullPointerException.class, () -> list.insertAll(0, null));
    }

    // === REMOVE TESTS ===

    @Test
    void remove_removesElementAtIndex() {
        TextElementList list = TextElementList.of(space(), newline(), tab());

        list.remove(1);

        assertEquals(2, list.size());
        assertTrue(list.get(0).isSpaceOrTab());
        assertTrue(list.get(1).isSpaceOrTab());
    }

    @Test
    void remove_withInvalidIndex_throwsIndexOutOfBoundsException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(IndexOutOfBoundsException.class, () -> list.remove(-1));
        assertThrows(IndexOutOfBoundsException.class, () -> list.remove(10));
    }

    // === REMOVE RANGE TESTS ===

    @Test
    void removeRange_removesInclusiveRange() {
        TextElementList list = TextElementList.of(space(), newline(), tab(), space(), newline());

        list.removeRange(1, 3);

        assertEquals(2, list.size());
        assertTrue(list.get(0).isSpaceOrTab());
        assertTrue(list.get(1).isNewline());
    }

    @Test
    void removeRange_withSingleElement_removesOne() {
        TextElementList list = TextElementList.of(space(), newline(), tab());

        list.removeRange(1, 1);

        assertEquals(2, list.size());
    }

    @Test
    void removeRange_withInvalidIndices_throwsIndexOutOfBoundsException() {
        TextElementList list = TextElementList.of(space(), newline());

        assertThrows(IndexOutOfBoundsException.class, () -> list.removeRange(-1, 0));
        assertThrows(IndexOutOfBoundsException.class, () -> list.removeRange(0, 10));
        assertThrows(IndexOutOfBoundsException.class, () -> list.removeRange(1, 0));
    }

    // === ACCESS TESTS ===

    @Test
    void get_returnsElementAtIndex() {
        TokenTextElement expected = newline();
        TextElementList list = TextElementList.of(space(), expected, tab());

        TextElement actual = list.get(1);

        assertEquals(expected, actual);
    }

    @Test
    void get_withInvalidIndex_throwsIndexOutOfBoundsException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(IndexOutOfBoundsException.class, () -> list.get(-1));
        assertThrows(IndexOutOfBoundsException.class, () -> list.get(10));
    }

    @Test
    void isValidIndex_returnsTrueForValidIndices() {
        TextElementList list = TextElementList.of(space(), newline());

        assertTrue(list.isValidIndex(0));
        assertTrue(list.isValidIndex(1));
    }

    @Test
    void isValidIndex_returnsFalseForInvalidIndices() {
        TextElementList list = TextElementList.of(space());

        assertFalse(list.isValidIndex(-1));
        assertFalse(list.isValidIndex(1));
        assertFalse(list.isValidIndex(10));
    }

    @Test
    void size_returnsCorrectSize() {
        TextElementList list = TextElementList.of(space(), newline(), tab());

        assertEquals(3, list.size());
    }

    @Test
    void isEmpty_returnsTrueForEmptyList() {
        TextElementList list = TextElementList.empty();

        assertTrue(list.isEmpty());
    }

    @Test
    void isEmpty_returnsFalseForNonEmptyList() {
        TextElementList list = TextElementList.of(space());

        assertFalse(list.isEmpty());
    }

    @Test
    void toList_returnsUnmodifiableView() {
        TextElementList list = TextElementList.of(space());
        List<TextElement> view = list.toList();

        assertThrows(UnsupportedOperationException.class, () -> view.add(newline()));
    }

    @Test
    void toList_reflectsChanges() {
        List<TextElement> original = new ArrayList<>(Arrays.asList(space()));
        TextElementList list = new TextElementList(original);
        List<TextElement> view = list.toList();

        original.add(newline());

        assertEquals(2, view.size());
    }

    // === ITERATOR TESTS ===

    @Test
    void iterator_iteratesOverAllElements() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator();

        int count = 0;
        while (iterator.hasNext()) {
            iterator.next();
            count++;
        }

        assertEquals(3, count);
    }

    @Test
    void iteratorFromIndex_startsAtSpecifiedIndex() {
        TextElementList list = TextElementList.of(space(), newline(), tab());
        TextElementIterator iterator = list.iterator(1);

        assertEquals(-1, iterator.currentIndex());
        assertTrue(iterator.next().isNewline());
    }

    @Test
    void iteratorFromIndex_withInvalidIndex_throwsIndexOutOfBoundsException() {
        TextElementList list = TextElementList.of(space());

        assertThrows(IndexOutOfBoundsException.class, () -> list.iterator(-1));
        assertThrows(IndexOutOfBoundsException.class, () -> list.iterator(10));
    }

    // === STREAM TESTS ===

    @Test
    void stream_returnsStreamOfElements() {
        TextElementList list = TextElementList.of(space(), newline(), tab(), space());

        long count = list.stream().filter(TextElement::isSpaceOrTab).count();

        assertEquals(3, count);
    }

    // === EQUALITY TESTS ===

    @Test
    void equals_returnsTrueForSameContent() {
        TextElementList list1 = TextElementList.of(space(), newline());
        TextElementList list2 = TextElementList.of(space(), newline());

        assertEquals(list1, list2);
    }

    @Test
    void equals_returnsFalseForDifferentContent() {
        TextElementList list1 = TextElementList.of(space());
        TextElementList list2 = TextElementList.of(newline());

        assertNotEquals(list1, list2);
    }

    @Test
    void hashCode_isConsistentWithEquals() {
        TextElementList list1 = TextElementList.of(space(), newline());
        TextElementList list2 = TextElementList.of(space(), newline());

        assertEquals(list1.hashCode(), list2.hashCode());
    }

    // === TESTS FOR anyMatch() ===

    @Test
    void anyMatch_withMatchingElement_returnsTrue() {
        TextElementList list = TextElementList.of(space(), token("test"), newline());

        assertTrue(list.anyMatch(el -> el instanceof TokenTextElement));
    }

    @Test
    void anyMatch_withNoMatchingElement_returnsFalse() {
        TextElementList list = TextElementList.of(space(), space(), newline());

        assertFalse(list.anyMatch(el -> el.match(token("test"))));
    }

    @Test
    void anyMatch_withEmptyList_returnsFalse() {
        TextElementList list = new TextElementList(new ArrayList<>());
        assertFalse(list.anyMatch(TextElement::isComment));
    }

    @Test
    void anyMatch_withNullPredicate_throwsException() {
        TextElementList list = TextElementList.of(space());
        assertThrows(NullPointerException.class, () -> list.anyMatch(null));
    }

    @Test
    void anyMatch_shortCircuits() {
        // Verify that anyMatch stops as soon as it finds a match
        List<TextElement> elements = new ArrayList<>();
        elements.add(space());
        elements.add(token("test")); // Should match here
        elements.add(newline());

        TextElementList list = new TextElementList(elements);

        AtomicInteger callCount = new AtomicInteger(0);
        boolean result = list.anyMatch(el -> {
            callCount.incrementAndGet();
            return el.match(token("test"));
        });

        assertTrue(result);
        // Should only call 2 times (space, then identifier which matches)
        assertEquals(2, callCount.get());
    }

    @Test
    void anyMatch_withComplexPredicate_worksCorrectly() {
        TextElementList list = TextElementList.of(space(), token("myVariable"), space(), token("otherVar"));

        boolean hasSpecificText = list.anyMatch(el -> el instanceof TokenTextElement
                && ((TokenTextElement) el).getText().equals("myVariable"));

        assertTrue(hasSpecificText);
    }

    // === TESTS FOR allMatch() ===

    @Test
    void allMatch_whenAllElementsMatch_returnsTrue() {
        TextElementList list = TextElementList.of(space(), space(), space());

        assertTrue(list.allMatch(TextElement::isSpaceOrTab));
    }

    @Test
    void allMatch_whenNotAllElementsMatch_returnsFalse() {
        TextElementList list = TextElementList.of(space(), token("test"), space());

        assertFalse(list.allMatch(TextElement::isSpaceOrTab));
    }

    @Test
    void allMatch_withEmptyList_returnsTrue() {
        // Empty list satisfies vacuous truth
        TextElementList list = new TextElementList(new ArrayList<>());
        assertTrue(list.allMatch(el -> false));
    }

    @Test
    void allMatch_withNullPredicate_throwsException() {
        TextElementList list = TextElementList.of(space());
        assertThrows(NullPointerException.class, () -> list.allMatch(null));
    }

    @Test
    void allMatch_shortCircuits() {
        // Verify that allMatch stops as soon as it finds a non-match
        List<TextElement> elements = new ArrayList<>();
        elements.add(space());
        elements.add(token("test")); // Should fail here
        elements.add(space());

        TextElementList list = new TextElementList(elements);

        AtomicInteger callCount = new AtomicInteger(0);
        boolean result = list.allMatch(el -> {
            callCount.incrementAndGet();
            return el.isSpaceOrTab();
        });

        assertFalse(result);
        // Should only call 2 times (space passes, then identifier fails)
        assertEquals(2, callCount.get());
    }

    @Test
    void allMatch_withComplexPredicate_worksCorrectly() {
        TextElementList list = TextElementList.of(space(), space(), newline());

        boolean allWhitespace = list.allMatch(el -> el.isSpaceOrTab() || el.isNewline());

        assertTrue(allWhitespace);
    }

    // === TESTS FOR noneMatch() ===

    @Test
    void noneMatch_whenNoElementsMatch_returnsTrue() {
        TextElementList list = TextElementList.of(space(), space(), newline());

        assertTrue(list.noneMatch(el -> el.match(token("test"))));
    }

    @Test
    void noneMatch_whenSomeElementsMatch_returnsFalse() {
        TextElementList list = TextElementList.of(space(), token("test"), newline());

        assertFalse(list.noneMatch(el -> el.match(token("test"))));
    }

    @Test
    void noneMatch_withEmptyList_returnsTrue() {
        TextElementList list = new TextElementList(new ArrayList<>());
        assertTrue(list.noneMatch(el -> true));
    }

    @Test
    void noneMatch_withNullPredicate_throwsException() {
        TextElementList list = TextElementList.of(space());
        assertThrows(NullPointerException.class, () -> list.noneMatch(null));
    }

    @Test
    void noneMatch_shortCircuits() {
        // Verify that noneMatch stops as soon as it finds a match
        List<TextElement> elements = new ArrayList<>();
        elements.add(space());
        elements.add(token("test")); // Should match here
        elements.add(newline());

        TextElementList list = new TextElementList(elements);

        AtomicInteger callCount = new AtomicInteger(0);
        boolean result = list.noneMatch(el -> {
            callCount.incrementAndGet();
            return el.match(token("test"));
        });

        assertFalse(result);
        // Should only call 2 times (space, then identifier which matches)
        assertEquals(2, callCount.get());
    }

    @Test
    void noneMatch_equivalentToNotAnyMatch() {
        TextElementList list = TextElementList.of(space(), token("test"), newline());

        Predicate<TextElement> predicate = TextElement::isComment;

        assertEquals(!list.anyMatch(predicate), list.noneMatch(predicate));
    }

    // === INTEGRATION TESTS ===

    @Test
    void matchingMethods_workTogetherCorrectly() {
        TextElementList list = TextElementList.of(space(), space(), token("test"), space());

        // Some are spaces
        assertTrue(list.anyMatch(TextElement::isSpaceOrTab));

        // Not all are spaces
        assertFalse(list.allMatch(TextElement::isSpaceOrTab));

        // None are comments
        assertTrue(list.noneMatch(TextElement::isComment));
    }

    @Test
    void matchingMethods_withSingleElement() {
        TextElementList list = TextElementList.of(space());

        assertTrue(list.anyMatch(TextElement::isSpaceOrTab));
        assertTrue(list.allMatch(TextElement::isSpaceOrTab));
        assertFalse(list.noneMatch(TextElement::isSpaceOrTab));
    }

    @Test
    void matchingMethods_performanceTest() {
        // Create a large list
        List<TextElement> elements = new ArrayList<>();
        for (int i = 0; i < 10000; i++) {
            elements.add(space());
        }
        // Add one token at the end
        elements.add(token("test"));

        TextElementList list = new TextElementList(elements);

        // anyMatch should find it quickly
        long start = System.nanoTime();
        boolean hasToken = list.anyMatch(el -> el instanceof TokenTextElement);
        long duration = System.nanoTime() - start;

        assertTrue(hasToken);
        // Should be fast (no specific assertion on time, just verify it works)
    }
}
