package com.github.javaparser;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

public class PositionTest {

    @Test
    public void testOrIfInvalid() {
        Position p1 = new Position(1, 1);
        Position p2 = new Position(2, 2);

        assertEquals(p1, p1.orIfInvalid(p2));

        Position invalid = new Position(0, 0);
        Position invalid2 = new Position(0, 1);

        assertEquals(p1, invalid.orIfInvalid(p1));
        assertEquals(invalid2, invalid2.orIfInvalid(invalid));
    }

    @Test
    public void testPositionExceptionMessage() {
        try {
            Position p = new Position(-10, 1);
            fail("Created " + p + " without exception.");
        } catch (IllegalArgumentException e) {
            assertEquals("Can't position at line -10", e.getMessage());
        }

        try {
            Position p = new Position(1, -10);
            fail("Created " + p + " without exception.");
        } catch (IllegalArgumentException e) {
            assertEquals("Can't position at column -10", e.getMessage());
        }
    }

}
