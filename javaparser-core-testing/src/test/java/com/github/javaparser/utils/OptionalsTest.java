package com.github.javaparser.utils;

import static org.junit.jupiter.api.Assertions.*;

import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Supplier;
import org.junit.jupiter.api.Test;

/**
 * Tests for Optionals utility class.
 */
class OptionalsTest {

    // =========================================================================
    // or() method tests - Basic functionality
    // =========================================================================

    @Test
    void orReturnsFirstPresentOptional() {
        Optional<String> result =
                Optionals.or(() -> Optional.of("first"), () -> Optional.of("second"), () -> Optional.of("third"));

        assertTrue(result.isPresent());
        assertEquals("first", result.get());
    }

    @Test
    void orReturnsSecondWhenFirstIsEmpty() {
        Optional<String> result =
                Optionals.or(() -> Optional.empty(), () -> Optional.of("second"), () -> Optional.of("third"));

        assertTrue(result.isPresent());
        assertEquals("second", result.get());
    }

    @Test
    void orReturnsEmptyWhenAllAreEmpty() {
        Optional<String> result = Optionals.or(() -> Optional.empty(), () -> Optional.empty(), () -> Optional.empty());

        assertFalse(result.isPresent());
    }

    @Test
    void orWithSingleSupplier() {
        Optional<String> result = Optionals.or(() -> Optional.of("only"));

        assertTrue(result.isPresent());
        assertEquals("only", result.get());
    }

    @Test
    void orWithNoSuppliers() {
        Optional<String> result = Optionals.or();

        assertFalse(result.isPresent());
    }

    // =========================================================================
    // or() method tests - Lazy evaluation (short-circuit)
    // =========================================================================

    @Test
    void orDoesNotEvaluateSubsequentSuppliersAfterFindingPresent() {
        AtomicInteger callCount = new AtomicInteger(0);

        Optional<String> result = Optionals.or(
                () -> {
                    callCount.incrementAndGet();
                    return Optional.of("first");
                },
                () -> {
                    callCount.incrementAndGet();
                    return Optional.of("second");
                },
                () -> {
                    callCount.incrementAndGet();
                    return Optional.of("third");
                });

        assertTrue(result.isPresent());
        assertEquals("first", result.get());
        assertEquals(1, callCount.get(), "Should only evaluate first supplier");
    }

    @Test
    void orEvaluatesUntilFirstPresent() {
        AtomicInteger callCount = new AtomicInteger(0);

        Optional<String> result = Optionals.or(
                () -> {
                    callCount.incrementAndGet();
                    return Optional.empty();
                },
                () -> {
                    callCount.incrementAndGet();
                    return Optional.empty();
                },
                () -> {
                    callCount.incrementAndGet();
                    return Optional.of("third");
                },
                () -> {
                    callCount.incrementAndGet();
                    return Optional.of("fourth");
                });

        assertTrue(result.isPresent());
        assertEquals("third", result.get());
        assertEquals(3, callCount.get(), "Should evaluate until finding present");
    }

    // =========================================================================
    // or() method tests - Type compatibility
    // =========================================================================

    @Test
    void orWorksWithDifferentTypes() {
        Optional<Integer> result = Optionals.or(() -> Optional.empty(), () -> Optional.of(42), () -> Optional.of(100));

        assertTrue(result.isPresent());
        assertEquals(42, result.get());
    }

    @Test
    void orWorksWithNullableOptionals() {
        Optional<String> result = Optionals.or(
                () -> Optional.ofNullable(null), () -> Optional.ofNullable("value"), () -> Optional.of("fallback"));

        assertTrue(result.isPresent());
        assertEquals("value", result.get());
    }

    // =========================================================================
    // or() method tests - Real-world usage patterns
    // =========================================================================

    @Test
    void orUsedForFallbackChain() {
        // Simulates checking multiple sources for a value
        Supplier<Optional<String>> checkCache = () -> Optional.empty();
        Supplier<Optional<String>> checkDatabase = () -> Optional.empty();
        Supplier<Optional<String>> checkDefault = () -> Optional.of("default");

        Optional<String> result = Optionals.or(checkCache, checkDatabase, checkDefault);

        assertTrue(result.isPresent());
        assertEquals("default", result.get());
    }

    @Test
    void orUsedForContextDetection() {
        // Simulates TokenOwnerDetector pattern
        class TestNode {
            String type;

            TestNode(String type) {
                this.type = type;
            }
        }

        TestNode node = new TestNode("field");

        Supplier<Optional<TestNode>> checkVariable =
                () -> node.type.equals("variable") ? Optional.of(node) : Optional.empty();
        Supplier<Optional<TestNode>> checkParameter =
                () -> node.type.equals("parameter") ? Optional.of(node) : Optional.empty();
        Supplier<Optional<TestNode>> checkField =
                () -> node.type.equals("field") ? Optional.of(node) : Optional.empty();

        Optional<TestNode> owner = Optionals.or(checkVariable, checkParameter, checkField);

        assertTrue(owner.isPresent());
        assertEquals("field", owner.get().type);
    }

    // =========================================================================
    // or() method tests - Edge cases
    // =========================================================================

    @Test
    void orWithExpensiveComputation() {
        AtomicInteger expensiveCallCount = new AtomicInteger(0);

        Supplier<Optional<String>> expensiveOperation = () -> {
            expensiveCallCount.incrementAndGet();
            // Simulate expensive operation
            try {
                Thread.sleep(1);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            return Optional.of("expensive");
        };

        Optional<String> result = Optionals.or(() -> Optional.of("cheap"), expensiveOperation);

        assertEquals("cheap", result.get());
        assertEquals(0, expensiveCallCount.get(), "Expensive operation should not be called");
    }

    @Test
    void orPreservesOrderOfEvaluation() {
        StringBuilder order = new StringBuilder();

        Optional<String> result = Optionals.or(
                () -> {
                    order.append("1");
                    return Optional.empty();
                },
                () -> {
                    order.append("2");
                    return Optional.empty();
                },
                () -> {
                    order.append("3");
                    return Optional.of("found");
                },
                () -> {
                    order.append("4");
                    return Optional.of("not-reached");
                });

        assertEquals("found", result.get());
        assertEquals("123", order.toString(), "Should evaluate in order and stop at first present");
    }

    // =========================================================================
    // Comparison with Java 9+ Optional.or() behavior
    // =========================================================================

    @Test
    void orEmulatesJava9OptionalOrBehavior() {
        // This test documents the equivalence with Java 9+ Optional.or()
        // Java 9+ code would be:
        // Optional<String> result = opt1.or(() -> opt2).or(() -> opt3);

        Optional<String> opt1 = Optional.empty();
        Optional<String> opt2 = Optional.empty();
        Optional<String> opt3 = Optional.of("value");

        // Our implementation:
        Optional<String> result = Optionals.or(() -> opt1, () -> opt2, () -> opt3);

        assertTrue(result.isPresent());
        assertEquals("value", result.get());
    }
}
