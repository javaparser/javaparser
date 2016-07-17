package com.github.javaparser.junit;

import org.junit.Test;

public class PrintingTheCompilationUnitToSystemOutputTest {
    @Test
    public void printingTheCompilationUnitToSystemOutput() throws Exception {
        try (TestFileToken f = new TestFileToken("test.java")) {
            CuPrinter.main(new String[]{});
        }
    }

}
