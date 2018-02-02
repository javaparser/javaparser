/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */

package com.github.javaparser.utils;

import java.io.IOException;
import java.io.Reader;
import java.util.*;
import java.util.function.Predicate;
import java.util.function.Function;

import static java.util.Arrays.*;

/**
 * Any kind of utility.
 *
 * @author Federico Tomassetti
 */
public class Utils {
    public static final String EOL = System.getProperty("line.separator");

    public static final Predicate<String> STRING_NOT_EMPTY = s -> !s.isEmpty();

    /**
     * @deprecated This is no longer in use by JavaParser, please write your own replacement.
     */
    public static <T> List<T> ensureNotNull(List<T> list) {
        return list == null ? new ArrayList<>() : list;
    }

    public static <E> boolean isNullOrEmpty(Collection<E> collection) {
        return collection == null || collection.isEmpty();
    }

    public static <T> T assertNotNull(T o) {
        if (o == null) {
            throw new AssertionError("A reference was unexpectedly null.");
        }
        return o;
    }

    public static String assertNonEmpty(String string) {
        if (string == null || string.isEmpty()) {
            throw new AssertionError("A string was unexpectedly empty.");
        }
        return string;
    }

    /**
     * @return string with ASCII characters 10 and 13 replaced by the text "\n" and "\r".
     */
    public static String escapeEndOfLines(String string) {
        StringBuilder escapedString = new StringBuilder();
        for (char c : string.toCharArray()) {
            switch (c) {
                case '\n':
                    escapedString.append("\\n");
                    break;
                case '\r':
                    escapedString.append("\\r");
                    break;
                default:
                    escapedString.append(c);
            }
        }
        return escapedString.toString();
    }

    public static String readerToString(Reader reader) throws IOException {
        final StringBuilder result = new StringBuilder();
        final char[] buffer = new char[8 * 1024];
        int numChars;

        while ((numChars = reader.read(buffer, 0, buffer.length)) > 0) {
            result.append(buffer, 0, numChars);
        }

        return result.toString();
    }

    /**
     * Puts varargs in a mutable list.
     * This does not have the disadvantage of Arrays#asList that it has a static size.
     *
     * @deprecated This is no longer in use by JavaParser, please write your own replacement.
     */
    @Deprecated
    public static <T> List<T> arrayToList(T[] array) {
        List<T> list = new LinkedList<>();
        Collections.addAll(list, array);
        return list;
    }

    /**
     * @deprecated use screamingToCamelCase
     */
    public static String toCamelCase(String original) {
        return screamingToCamelCase(original);
    }

    /**
     * Transform a string to the camel case conversion.
     * <p>
     * For example "ABC_DEF" becomes "abcDef"
     */
    public static String screamingToCamelCase(String original) {
        StringBuilder sb = new StringBuilder();
        String[] parts = original.toLowerCase().split("_");
        for (int i = 0; i < parts.length; i++) {
            sb.append(i == 0 ? parts[i] : capitalize(parts[i]));
        }
        return sb.toString();
    }


    /**
     * @param input "aCamelCaseString"
     * @return "A_CAMEL_CASE_STRING"
     */
    public static String camelCaseToScreaming(String input) {
        if (input.isEmpty()) {
            return "";
        }
        StringBuilder scream = new StringBuilder(input.substring(0, 1).toUpperCase());
        for (char c : input.substring(1).toCharArray()) {
            if (Character.isUpperCase(c)) {
                scream.append("_");
            }
            scream.append(Character.toUpperCase(c));
        }
        return scream.toString();
    }

    /**
     * Return the next word of the string, in other words it stops when a space is encountered.
     */
    public static String nextWord(String string) {
        int index = 0;
        while (index < string.length() && !Character.isWhitespace(string.charAt(index))) {
            index++;
        }
        return string.substring(0, index);
    }

    /**
     * Make an indent by appending indentLevel tab characters to the builder.
     */
    public static StringBuilder indent(StringBuilder builder, int indentLevel) {
        for (int i = 0; i < indentLevel; i++) {
            builder.append("\t");
        }
        return builder;
    }

    /**
     * Capitalizes the first character in the string.
     */
    public static String capitalize(String s) {
        return stringTransformer(s, "capitalize", String::toUpperCase);
    }

    /**
     * Lower-cases the first character in the string.
     */
    public static String decapitalize(String s) {
        return stringTransformer(s, "decapitalize", String::toLowerCase);
    }

    private static String stringTransformer(String s, String operationDescription, Function<String, String> transformation) {
        if (s.isEmpty()) {
            throw new IllegalArgumentException(String.format("You cannot %s an empty string", operationDescription));
        }
        return transformation.apply(s.substring(0, 1)) +
                s.substring(1);
    }

    /**
     * @return true if the value is null, an empty Optional, or an empty String.
     */
    public static boolean valueIsNullOrEmpty(Object value) {
        if (value == null) {
            return true;
        }
        if (value instanceof Optional) {
            if (((Optional) value).isPresent()) {
                value = ((Optional) value).get();
            } else {
                return true;
            }
        }
        if (value instanceof Collection) {
            if (((Collection) value).isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return a set of the items.
     */
    public static <T> Set<T> set(T... items) {
        return new HashSet<>(asList(items));
    }

    /**
     * @return content with all kinds of EOL characters replaced by endOfLineCharacter
     */
    public static String normalizeEolInTextBlock(String content, String endOfLineCharacter) {
        return content
                .replaceAll("\\R", endOfLineCharacter);
    }

    /**
     * @return the filename with the last "." and everything following it removed.
     */
    public static String removeFileExtension(String filename) {
        int extensionIndex = filename.lastIndexOf(".");
        if (extensionIndex == -1)
            return filename;

        return filename.substring(0, extensionIndex);
    }

    /**
     * Like {@link String#trim()}, but only the trailing spaces.
     */
    public static String trimTrailingSpaces(String line) {
        while (line.length() > 0 && line.charAt(line.length() - 1) <= 0x20) {
            line = line.substring(0, line.length() - 1);
        }
        return line;
    }

}
