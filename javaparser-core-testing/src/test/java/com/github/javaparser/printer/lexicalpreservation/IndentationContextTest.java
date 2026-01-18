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
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

class IndentationContextTest {

    private IndentationContext context;

    @BeforeEach
    void setUp() {
        context = new IndentationContext();
    }

    // Helper method to create a space token
    private TokenTextElement space() {
        return new TokenTextElement(GeneratedJavaParserConstants.SPACE, " ");
    }

    // Helper method to create a tab token
    private TokenTextElement tab() {
        return new TokenTextElement(GeneratedJavaParserConstants.SPACE, "\t");
    }

    @Nested
    @DisplayName("Constructor tests")
    class ConstructorTests {

        @Test
        @DisplayName("Should create context with empty indentation by default")
        void defaultConstructor() {
            IndentationContext ctx = new IndentationContext();

            assertEquals(0, ctx.size());
            assertTrue(ctx.getCurrent().isEmpty());
        }

        @Test
        @DisplayName("Should create context with provided initial indentation")
        void constructorWithInitialIndentation() {
            List<TextElement> initial = Arrays.asList(space(), space(), space(), space());

            IndentationContext ctx = new IndentationContext(initial);

            assertEquals(4, ctx.size());
            assertEquals(4, ctx.getCurrent().size());
        }

        @Test
        @DisplayName("Should copy initial indentation not reference it")
        void constructorCopiesInitialIndentation() {
            List<TextElement> initial = new ArrayList<>(Arrays.asList(space(), space()));

            IndentationContext ctx = new IndentationContext(initial);
            initial.clear(); // Modify original list

            assertEquals(2, ctx.size()); // Context should still have 2 elements
        }

        @Test
        @DisplayName("Should handle empty initial indentation")
        void constructorWithEmptyIndentation() {
            List<TextElement> initial = new ArrayList<>();

            IndentationContext ctx = new IndentationContext(initial);

            assertEquals(0, ctx.size());
            assertTrue(ctx.getCurrent().isEmpty());
        }
    }

    @Nested
    @DisplayName("Increase indentation tests")
    class IncreaseTests {

        @Test
        @DisplayName("Should increase indentation by 4 spaces")
        void increaseOnce() {
            context.increase();

            assertEquals(4, context.size());
            List<TextElement> current = context.getCurrent();
            assertEquals(4, current.size());
            assertTrue(current.stream().allMatch(e -> e.isSpaceOrTab()));
        }

        @Test
        @DisplayName("Should increase indentation multiple times")
        void increaseMultipleTimes() {
            context.increase();
            context.increase();
            context.increase();

            assertEquals(12, context.size());
        }

        @Test
        @DisplayName("Should add exactly STANDARD_INDENTATION_SIZE spaces each time")
        void increaseAddsStandardSize() {
            int initialSize = context.size();

            context.increase();

            assertEquals(initialSize + IndentationConstants.STANDARD_INDENTATION_SIZE, context.size());
        }

        @Test
        @DisplayName("Should maintain existing indentation when increasing")
        void increasePreservesExisting() {
            context.increase(); // 4 spaces
            int sizeAfterFirst = context.size();

            context.increase(); // 4 more spaces

            assertEquals(sizeAfterFirst + IndentationConstants.STANDARD_INDENTATION_SIZE, context.size());
        }
    }

    @Nested
    @DisplayName("Decrease indentation tests")
    class DecreaseTests {

        @Test
        @DisplayName("Should decrease indentation by 4 spaces")
        void decreaseOnce() {
            context.increase();
            context.increase(); // 8 spaces

            context.decrease(); // Remove 4 spaces

            assertEquals(4, context.size());
        }

        @Test
        @DisplayName("Should not go below zero when decreasing empty indentation")
        void decreaseWhenEmpty() {
            context.decrease();

            assertEquals(0, context.size());
            assertTrue(context.getCurrent().isEmpty());
        }

        @Test
        @DisplayName("Should handle partial decrease when fewer elements than standard size")
        void decreaseWithPartialIndentation() {
            // Add only 2 spaces manually
            context.set(Arrays.asList(space(), space()));

            context.decrease(); // Try to remove 4 but only 2 exist

            assertEquals(0, context.size());
        }

        @Test
        @DisplayName("Should decrease multiple times correctly")
        void decreaseMultipleTimes() {
            context.increase();
            context.increase();
            context.increase(); // 12 spaces

            context.decrease(); // 8 spaces
            context.decrease(); // 4 spaces

            assertEquals(4, context.size());
        }

        @Test
        @DisplayName("Should remove exactly STANDARD_INDENTATION_SIZE spaces each time")
        void decreaseRemovesStandardSize() {
            context.increase();
            context.increase(); // 8 spaces
            int initialSize = context.size();

            context.decrease();

            assertEquals(initialSize - IndentationConstants.STANDARD_INDENTATION_SIZE, context.size());
        }
    }

    @Nested
    @DisplayName("Get current indentation tests")
    class GetCurrentTests {

        @Test
        @DisplayName("Should return empty list for new context")
        void getCurrentEmpty() {
            List<TextElement> current = context.getCurrent();

            assertNotNull(current);
            assertTrue(current.isEmpty());
        }

        @Test
        @DisplayName("Should return copy of current indentation")
        void getCurrentReturnsCopy() {
            context.increase();

            List<TextElement> current = context.getCurrent();

            assertEquals(4, current.size());
            assertNotSame(current, context.getCurrent()); // Different instances
        }

        @Test
        @DisplayName("Should return unmodifiable list")
        void getCurrentIsUnmodifiable() {
            context.increase();
            List<TextElement> current = context.getCurrent();

            assertThrows(UnsupportedOperationException.class, () -> {
                current.add(space());
            });
        }

        @Test
        @DisplayName("Should reflect changes after increase")
        void getCurrentReflectsIncrease() {
            List<TextElement> before = context.getCurrent();
            assertEquals(0, before.size());

            context.increase();

            List<TextElement> after = context.getCurrent();
            assertEquals(4, after.size());
        }

        @Test
        @DisplayName("Should reflect changes after decrease")
        void getCurrentReflectsDecrease() {
            context.increase();
            context.increase();
            assertEquals(8, context.getCurrent().size());

            context.decrease();

            assertEquals(4, context.getCurrent().size());
        }
    }

    @Nested
    @DisplayName("Size tests")
    class SizeTests {

        @Test
        @DisplayName("Should return zero for new context")
        void sizeInitiallyZero() {
            assertEquals(0, context.size());
        }

        @Test
        @DisplayName("Should return correct size after increase")
        void sizeAfterIncrease() {
            context.increase();
            assertEquals(4, context.size());

            context.increase();
            assertEquals(8, context.size());
        }

        @Test
        @DisplayName("Should return correct size after decrease")
        void sizeAfterDecrease() {
            context.increase();
            context.increase();
            context.decrease();

            assertEquals(4, context.size());
        }

        @Test
        @DisplayName("Should match getCurrent list size")
        void sizeMatchesCurrentSize() {
            context.increase();

            assertEquals(context.getCurrent().size(), context.size());
        }
    }

    @Nested
    @DisplayName("Clear tests")
    class ClearTests {

        @Test
        @DisplayName("Should clear all indentation")
        void clearAll() {
            context.increase();
            context.increase();

            context.clear();

            assertEquals(0, context.size());
            assertTrue(context.getCurrent().isEmpty());
        }

        @Test
        @DisplayName("Should do nothing when clearing empty context")
        void clearEmpty() {
            context.clear();

            assertEquals(0, context.size());
            assertTrue(context.getCurrent().isEmpty());
        }

        @Test
        @DisplayName("Should allow operations after clear")
        void operationsAfterClear() {
            context.increase();
            context.clear();

            context.increase();

            assertEquals(4, context.size());
        }
    }

    @Nested
    @DisplayName("Set tests")
    class SetTests {

        @Test
        @DisplayName("Should replace current indentation")
        void setReplaces() {
            context.increase(); // 4 spaces

            List<TextElement> newIndent = Arrays.asList(tab(), tab());
            context.set(newIndent);

            assertEquals(2, context.size());
        }

        @Test
        @DisplayName("Should copy provided list not reference it")
        void setCopiesList() {
            List<TextElement> newIndent = new ArrayList<>(Arrays.asList(space(), space()));

            context.set(newIndent);
            newIndent.clear(); // Modify original

            assertEquals(2, context.size()); // Context should still have 2 elements
        }

        @Test
        @DisplayName("Should handle setting empty list")
        void setEmpty() {
            context.increase();

            context.set(new ArrayList<>());

            assertEquals(0, context.size());
            assertTrue(context.getCurrent().isEmpty());
        }

        @Test
        @DisplayName("Should completely replace previous content")
        void setReplacesAll() {
            context.increase();
            context.increase(); // 8 spaces

            List<TextElement> newIndent = Arrays.asList(tab());
            context.set(newIndent);

            assertEquals(1, context.size());
            List<TextElement> current = context.getCurrent();
            assertTrue(current.get(0).isSpaceOrTab());
        }
    }

    @Nested
    @DisplayName("Equals and hashCode tests")
    class EqualsHashCodeTests {

        @Test
        @DisplayName("Should be equal to itself")
        void equalsItself() {
            assertEquals(context, context);
        }

        @Test
        @DisplayName("Should be equal to context with same indentation")
        void equalsSameIndentation() {
            IndentationContext ctx1 = new IndentationContext();
            IndentationContext ctx2 = new IndentationContext();

            ctx1.increase();
            ctx2.increase();

            assertEquals(ctx1, ctx2);
        }

        @Test
        @DisplayName("Should not be equal to context with different indentation")
        void notEqualsDifferentIndentation() {
            IndentationContext ctx1 = new IndentationContext();
            IndentationContext ctx2 = new IndentationContext();

            ctx1.increase();
            ctx2.increase();
            ctx2.increase();

            assertNotEquals(ctx1, ctx2);
        }

        @Test
        @DisplayName("Should not be equal to null")
        void notEqualsNull() {
            assertNotEquals(context, null);
        }

        @Test
        @DisplayName("Should not be equal to different type")
        void notEqualsDifferentType() {
            assertNotEquals(context, "not a context");
        }

        @Test
        @DisplayName("Should have same hashCode for equal contexts")
        void hashCodeConsistent() {
            IndentationContext ctx1 = new IndentationContext();
            IndentationContext ctx2 = new IndentationContext();

            ctx1.increase();
            ctx2.increase();

            assertEquals(ctx1.hashCode(), ctx2.hashCode());
        }

        @Test
        @DisplayName("Empty contexts should be equal")
        void emptyContextsEqual() {
            IndentationContext ctx1 = new IndentationContext();
            IndentationContext ctx2 = new IndentationContext();

            assertEquals(ctx1, ctx2);
            assertEquals(ctx1.hashCode(), ctx2.hashCode());
        }
    }

    @Nested
    @DisplayName("ToString tests")
    class ToStringTests {

        @Test
        @DisplayName("Should contain size information")
        void toStringContainsSize() {
            context.increase();

            String str = context.toString();

            assertTrue(str.contains("size=4"));
        }

        @Test
        @DisplayName("Should be valid for empty context")
        void toStringEmpty() {
            String str = context.toString();

            assertNotNull(str);
            assertTrue(str.contains("IndentationContext"));
            assertTrue(str.contains("size=0"));
        }

        @Test
        @DisplayName("Should not throw exception")
        void toStringNoException() {
            assertDoesNotThrow(() -> context.toString());
        }
    }

    @Nested
    @DisplayName("Integration tests")
    class IntegrationTests {

        @Test
        @DisplayName("Should handle complex sequence of operations")
        void complexSequence() {
            context.increase(); // 4
            context.increase(); // 8
            context.decrease(); // 4
            context.increase(); // 8
            context.set(Arrays.asList(space(), space())); // 2
            context.increase(); // 6
            context.clear(); // 0
            context.increase(); // 4

            assertEquals(4, context.size());
        }

        @Test
        @DisplayName("Should maintain consistency across operations")
        void maintainConsistency() {
            for (int i = 0; i < 10; i++) {
                context.increase();
            }

            assertEquals(40, context.size());

            for (int i = 0; i < 5; i++) {
                context.decrease();
            }

            assertEquals(20, context.size());
            assertEquals(20, context.getCurrent().size());
        }

        @Test
        @DisplayName("Should support builder-style chaining via separate calls")
        void builderStyle() {
            context.increase();
            context.increase();

            assertEquals(8, context.size());

            context.decrease();

            assertEquals(4, context.size());
        }
    }

    @Nested
    @DisplayName("Edge cases")
    class EdgeCaseTests {

        @Test
        @DisplayName("Should handle many increase operations")
        void manyIncreases() {
            for (int i = 0; i < 100; i++) {
                context.increase();
            }

            assertEquals(400, context.size());
        }

        @Test
        @DisplayName("Should handle many decrease operations on empty")
        void manyDecreasesOnEmpty() {
            for (int i = 0; i < 100; i++) {
                context.decrease();
            }

            assertEquals(0, context.size());
        }

        @Test
        @DisplayName("Should handle set with mixed whitespace types")
        void setMixedWhitespace() {
            List<TextElement> mixed = Arrays.asList(space(), tab(), space(), tab());

            context.set(mixed);

            assertEquals(4, context.size());
            List<TextElement> current = context.getCurrent();
            assertTrue(current.stream().allMatch(e -> e.isSpaceOrTab()));
        }

        @Test
        @DisplayName("Should handle large indentation values")
        void largeIndentation() {
            List<TextElement> large = new ArrayList<>();
            for (int i = 0; i < 1000; i++) {
                large.add(space());
            }

            context.set(large);

            assertEquals(1000, context.size());
        }
    }
}
