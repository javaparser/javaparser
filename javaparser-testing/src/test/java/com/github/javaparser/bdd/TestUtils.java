package com.github.javaparser.bdd;

import java.io.InputStream;

public class TestUtils {

    public static InputStream getSampleStream(String sampleName) {
        InputStream is = TestUtils.class.getClassLoader().getResourceAsStream("com/github/javaparser/bdd/samples/"
                + sampleName + ".java");
        if (is == null) {
            throw new RuntimeException("Example not found, check your test. Sample name: " + sampleName);
        }
        return is;
    }

}
