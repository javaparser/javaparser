package com.github.javaparser.junit.wiki_samples;

import org.junit.Test;

public class ChangingMethodsFromAClassWithoutAVisitorTest {
    @Test
    public void printingTheCompilationUnitToSystemOutput() throws Exception {
        try (TestFileToken f = new TestFileToken("test.java")) {
            MethodChanger_2.main(new String[]{});
        }
    }
}
