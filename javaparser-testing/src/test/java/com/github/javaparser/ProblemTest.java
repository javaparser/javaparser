package com.github.javaparser;

import org.junit.Test;

import static com.github.javaparser.Range.range;
import static com.github.javaparser.utils.TestUtils.assertInstanceOf;
import static org.junit.Assert.assertEquals;

public class ProblemTest {
    @Test
    public void testSimpleGetters() {
        Problem problem = new Problem("Parse error", range(10, 10, 20, 20), new Exception());

        assertEquals(range(10, 10, 20, 20), problem.getLocation().get());
        assertEquals("Parse error", problem.getMessage());
        assertInstanceOf(Exception.class, problem.getCause().get());
    }

    @Test
    public void testVerboseMessage() {
        Problem problem = new Problem("Parse error", range(10, 10, 20, 20), null);

        assertEquals("Parse error at (line 10,col 10)", problem.getVerboseMessage());
    }
    @Test
    public void testVerboseMessageWithoutLocation() {
        Problem problem = new Problem("Parse error", null, null);

        assertEquals("Parse error", problem.getVerboseMessage());
    }
}