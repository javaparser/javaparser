package com.github.javaparser.generator.utils;

public class GeneratorUtils {
    public static String capitalize(String original) {
        if (original.isEmpty()) {
            return original;
        }
        return original.substring(0, 1).toUpperCase() + original.substring(1);
    }

    public static String decapitalize(String string) {
        if (string.isEmpty()) {
            return string;
        }
        return string.substring(0, 1).toLowerCase() + string.substring(1);
    }

    /**
     * A shortcut to String.format.
     */
    public static String f(String format, Object... params) {
        return String.format(format, params);
    }

}
