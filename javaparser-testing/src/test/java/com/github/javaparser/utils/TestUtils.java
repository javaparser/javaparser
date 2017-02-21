package com.github.javaparser.utils;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

public class TestUtils {
    /**
     * Takes care of setting all the end of line character to platform specific ones.
     */
    public static String readFileWith(String resourceName) throws IOException {
        try (final InputStream inputStream = TestUtils.class.getClassLoader().getResourceAsStream(resourceName);
             final BufferedReader br = new BufferedReader(new InputStreamReader(inputStream, "utf-8"))) {
            final StringBuilder builder = new StringBuilder();
            String line;
            while ((line = br.readLine()) != null) {
                builder.append(line).append(Utils.EOL);
            }
            return builder.toString();
        }
    }
}
