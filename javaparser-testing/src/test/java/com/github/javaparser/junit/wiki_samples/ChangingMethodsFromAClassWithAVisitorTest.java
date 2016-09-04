package com.github.javaparser.junit.wiki_samples;

import org.junit.Test;

public class ChangingMethodsFromAClassWithAVisitorTest {
    @Test
    public void printingTheCompilationUnitToSystemOutput() throws Exception {
        try (TestFileToken f = new TestFileToken("test.java")) {
            MethodChanger_1.main(new String[]{});
        }
    }
}
