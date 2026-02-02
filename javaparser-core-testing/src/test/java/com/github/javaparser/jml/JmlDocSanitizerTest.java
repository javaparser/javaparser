package com.github.javaparser.jml;

import java.util.Arrays;
import java.util.TreeSet;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (14.02.22)
 */
public class JmlDocSanitizerTest {
    private static final String EXAMPLE_INPUT =
            "//+key@ A\n" + "//+openjml@ B\n" + "//@ C\n" + "//-key@ D\n" + "/*+key@ E*/\n" + "/*+key+openjml@ F*/";

    @Test
    public void empty() {
        Assertions.assertEquals("            ", sanitize("/*+key@ A */", "openjml"));

        Assertions.assertEquals(
                "        A\n" + "             \n" + "    C\n" + "         \n" + "        E  \n" + "                F  ",
                sanitize(EXAMPLE_INPUT, "key"));

        Assertions.assertEquals(
                "         \n" + "            B\n" + "    C\n" + "        D\n" + "           \n" + "                F  ",
                sanitize(EXAMPLE_INPUT, "openjml"));
        Assertions.assertEquals(
                "         \n" + "             \n" + "    C\n" + "        D\n" + "           \n" + "                   ",
                sanitize(EXAMPLE_INPUT));
    }

    private String sanitize(String input, String... keys) {
        JmlDocSanitizer sanitizer = new JmlDocSanitizer(new TreeSet<>(Arrays.asList(keys)));
        return sanitizer.toSanitizedString(new StringBuilder(input));
    }
}
