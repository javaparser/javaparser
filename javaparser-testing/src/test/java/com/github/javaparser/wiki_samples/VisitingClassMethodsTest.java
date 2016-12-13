package com.github.javaparser.wiki_samples;

import org.junit.Test;

public class VisitingClassMethodsTest {
    @Test
    public void testCode() throws Exception {
        try (TestFileToken f = new TestFileToken("test.java")) {
            MethodPrinter.main(new String[]{});
        }
    }
}
