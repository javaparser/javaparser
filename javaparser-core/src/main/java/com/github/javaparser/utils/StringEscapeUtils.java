/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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
import java.io.StringWriter;
import java.io.Writer;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Adapted from apache commons-lang3 project.
 * <p>
 * Unescapes escaped chars in strings.
 */
public final class StringEscapeUtils {

    private StringEscapeUtils() {
    }

    /**
     * <p>Escapes the characters in a {@code String} using Java String rules.</p>
     * <p>
     * <p>Deals correctly with quotes and control-chars (tab, backslash, cr, ff, etc.) </p>
     * <p>
     * <p>So a tab becomes the characters {@code '\\'} and
     * {@code 't'}.</p>
     * <p>
     * <p>The only difference between Java strings and JavaScript strings
     * is that in JavaScript, a single quote and forward-slash (/) are escaped.</p>
     * <p>
     * <p>Example:</p>
     * <pre>
     * input string: He didn't say, "Stop!"
     * output string: He didn't say, \"Stop!\"
     * </pre>
     *
     * @param input String to escape values in, may be null
     * @return String with escaped values, {@code null} if null string input
     */
    public static String escapeJava(final String input) {
        return ESCAPE_JAVA.translate(input);
    }

    /**
     * <p>Unescapes any Java literals found in the {@code String}.
     * For example, it will turn a sequence of {@code '\'} and
     * {@code 'n'} into a newline character, unless the {@code '\'}
     * is preceded by another {@code '\'}.</p>
     * <p>
     * This can be replaced by String::translateEscapes in JDK 13
     *
     * @param input the {@code String} to unescape, may be null
     * @return a new unescaped {@code String}, {@code null} if null string input
     */
    public static String unescapeJava(final String input) {
        return UNESCAPE_JAVA.translate(input);
    }

    public static String unescapeJavaTextBlock(final String input) {
        return UNESCAPE_JAVA_TEXT_BLOCK.translate(input);
    }

    private static final LookupTranslator JAVA_CTRL_CHARS_UNESCAPE = new LookupTranslator(new String[][] { { "\\b", "\b" }, { "\\n", "\n" }, { "\\t", "\t" }, { "\\f", "\f" }, { "\\r", "\r" } });

    private static final LookupTranslator JAVA_CTRL_CHARS_ESCAPE = new LookupTranslator(new String[][] { { "\b", "\\b" }, { "\n", "\\n" }, { "\t", "\\t" }, { "\f", "\\f" }, { "\r", "\\r" } });

    private static final CharSequenceTranslator ESCAPE_JAVA = new AggregateTranslator(new LookupTranslator(new String[][] { { "\"", "\\\"" }, { "\\", "\\\\" } }), JAVA_CTRL_CHARS_ESCAPE);

    private static final CharSequenceTranslator UNESCAPE_JAVA = new AggregateTranslator(new OctalUnescaper(), new UnicodeUnescaper(), JAVA_CTRL_CHARS_UNESCAPE, new LookupTranslator(new String[][] { { "\\\\", "\\" }, { "\\\"", "\"" }, { "\\'", "'" }, { "\\", "" } }));

    private static final CharSequenceTranslator UNESCAPE_JAVA_TEXT_BLOCK = new AggregateTranslator(new OctalUnescaper(), new UnicodeUnescaper(), JAVA_CTRL_CHARS_UNESCAPE, new LookupTranslator(new String[][] { { "\\\\", "\\" }, { "\\\"", "\"" }, { "\\'", "'" }, { "\\", "" }, { "\\s", " " }, { "\\\n", "" } }));

    /**
     * Adapted from apache commons-lang3 project.
     * <p>
     * An API for translating text.
     * Its core use is to escape and unescape text. Because escaping and unescaping
     * is completely contextual, the API does not present two separate signatures.
     *
     * @since 3.0
     */
    private static abstract class CharSequenceTranslator {

        /**
         * Translate a set of codepoints, represented by an int index into a CharSequence,
         * into another set of codepoints. The number of codepoints consumed must be returned,
         * and the only IOExceptions thrown must be from interacting with the Writer so that
         * the top level API may reliably ignore StringWriter IOExceptions.
         *
         * @param input CharSequence that is being translated
         * @param index int representing the current point of translation
         * @param out Writer to translate the text to
         * @return int count of codepoints consumed
         * @throws IOException if and only if the Writer produces an IOException
         */
        protected abstract int translate(CharSequence input, int index, Writer out) throws IOException;

        /**
         * Helper for non-Writer usage.
         *
         * @param input CharSequence to be translated
         * @return String output of translation
         */
        private String translate(final CharSequence input) {
            if (input == null) {
                return null;
            }
            try {
                final StringWriter writer = new StringWriter(input.length() * 2);
                translate(input, writer);
                return writer.toString();
            } catch (final IOException ioe) {
                // this should never ever happen while writing to a StringWriter
                throw new RuntimeException(ioe);
            }
        }

        /**
         * Translate an input onto a Writer. This is intentionally final as its algorithm is
         * tightly coupled with the abstract method of this class.
         *
         * @param input CharSequence that is being translated
         * @param out Writer to translate the text to
         * @throws IOException if and only if the Writer produces an IOException
         */
        private void translate(final CharSequence input, final Writer out) throws IOException {
            if (out == null) {
                throw new IllegalArgumentException("The Writer must not be null");
            }
            if (input == null) {
                return;
            }
            int pos = 0;
            final int len = input.length();
            while (pos < len) {
                final int consumed = translate(input, pos, out);
                if (consumed == 0) {
                    // inlined implementation of Character.toChars(Character.codePointAt(input, pos))
                    // avoids allocating temp char arrays and duplicate checks
                    char c1 = input.charAt(pos);
                    out.write(c1);
                    pos++;
                    if (Character.isHighSurrogate(c1) && pos < len) {
                        char c2 = input.charAt(pos);
                        if (Character.isLowSurrogate(c2)) {
                            out.write(c2);
                            pos++;
                        }
                    }
                    continue;
                }
                // contract with translators is that they have to understand codepoints
                // and they just took care of a surrogate pair
                for (int pt = 0; pt < consumed; pt++) {
                    pos += Character.charCount(Character.codePointAt(input, pos));
                }
            }
        }
    }

    /**
     * Adapted from apache commons-lang3 project.
     * <p>
     * Translates a value using a lookup table.
     *
     * @since 3.0
     */
    private static class LookupTranslator extends CharSequenceTranslator {

        private final HashMap<String, String> lookupMap;

        private final HashSet<Character> prefixSet;

        private final int shortest;

        private final int longest;

        /**
         * Define the lookup table to be used in translation
         * <p>
         * Note that, as of Lang 3.1, the key to the lookup table is converted to a
         * java.lang.String. This is because we need the key to support hashCode and
         * equals(Object), allowing it to be the key for a HashMap. See LANG-882.
         *
         * @param lookup CharSequence[][] table of size [*][2]
         */
        private LookupTranslator(final CharSequence[]... lookup) {
            lookupMap = new HashMap<>();
            prefixSet = new HashSet<>();
            int _shortest = Integer.MAX_VALUE;
            int _longest = 0;
            if (lookup != null) {
                for (final CharSequence[] seq : lookup) {
                    this.lookupMap.put(seq[0].toString(), seq[1].toString());
                    this.prefixSet.add(seq[0].charAt(0));
                    final int sz = seq[0].length();
                    if (sz < _shortest) {
                        _shortest = sz;
                    }
                    if (sz > _longest) {
                        _longest = sz;
                    }
                }
            }
            shortest = _shortest;
            longest = _longest;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        protected int translate(final CharSequence input, final int index, final Writer out) throws IOException {
            // check if translation exists for the input at position index
            if (prefixSet.contains(input.charAt(index))) {
                int max = longest;
                if (index + longest > input.length()) {
                    max = input.length() - index;
                }
                // implement greedy algorithm by trying maximum match first
                for (int i = max; i >= shortest; i--) {
                    final CharSequence subSeq = input.subSequence(index, index + i);
                    final String result = lookupMap.get(subSeq.toString());
                    if (result != null) {
                        out.write(result);
                        return i;
                    }
                }
            }
            return 0;
        }
    }

    /**
     * Adapted from apache commons-lang3 project.
     * <p>
     * Executes a sequence of translators one after the other. Execution ends whenever
     * the first translator consumes codepoints from the input.
     *
     * @since 3.0
     */
    private static class AggregateTranslator extends CharSequenceTranslator {

        private final CharSequenceTranslator[] translators;

        /**
         * Specify the translators to be used at creation time.
         *
         * @param translators CharSequenceTranslator array to aggregate
         */
        private AggregateTranslator(final CharSequenceTranslator... translators) {
            this.translators = translators == null ? null : translators.clone();
        }

        /**
         * The first translator to consume codepoints from the input is the 'winner'.
         * Execution stops with the number of consumed codepoints being returned.
         * {@inheritDoc}
         */
        @Override
        protected int translate(final CharSequence input, final int index, final Writer out) throws IOException {
            for (final CharSequenceTranslator translator : translators) {
                final int consumed = translator.translate(input, index, out);
                if (consumed != 0) {
                    return consumed;
                }
            }
            return 0;
        }
    }

    /**
     * Adapted from apache commons-lang3 project.
     * <p>
     * Translate escaped octal Strings back to their octal values.
     * <p>
     * For example, "\45" should go back to being the specific value (a %).
     * <p>
     * Note that this currently only supports the viable range of octal for Java; namely
     * 1 to 377. This is because parsing Java is the main use case.
     *
     * @since 3.0
     */
    private static class OctalUnescaper extends CharSequenceTranslator {

        /**
         * {@inheritDoc}
         */
        @Override
        protected int translate(final CharSequence input, final int index, final Writer out) throws IOException {
            // how many characters left, ignoring the first \
            final int remaining = input.length() - index - 1;
            final StringBuilder builder = new StringBuilder();
            if (input.charAt(index) == '\\' && remaining > 0 && isOctalDigit(input.charAt(index + 1))) {
                final int next = index + 1;
                final int next2 = index + 2;
                final int next3 = index + 3;
                // we know this is good as we checked it in the if block above
                builder.append(input.charAt(next));
                if (remaining > 1 && isOctalDigit(input.charAt(next2))) {
                    builder.append(input.charAt(next2));
                    if (remaining > 2 && isZeroToThree(input.charAt(next)) && isOctalDigit(input.charAt(next3))) {
                        builder.append(input.charAt(next3));
                    }
                }
                out.write(Integer.parseInt(builder.toString(), 8));
                return 1 + builder.length();
            }
            return 0;
        }

        /**
         * Checks if the given char is an octal digit. Octal digits are the character representations of the digits 0 to
         * 7.
         *
         * @param ch the char to check
         * @return true if the given char is the character representation of one of the digits from 0 to 7
         */
        private boolean isOctalDigit(final char ch) {
            return ch >= '0' && ch <= '7';
        }

        /**
         * Checks if the given char is the character representation of one of the digit from 0 to 3.
         *
         * @param ch the char to check
         * @return true if the given char is the character representation of one of the digits from 0 to 3
         */
        private boolean isZeroToThree(final char ch) {
            return ch >= '0' && ch <= '3';
        }
    }

    /**
     * Adapted from apache commons-lang3 project.
     * <p>
     * Translates escaped Unicode values of the form \\u+\d\d\d\d back to
     * Unicode. It supports multiple 'u' characters and will work with or
     * without the +.
     *
     * @since 3.0
     */
    private static class UnicodeUnescaper extends CharSequenceTranslator {

        /**
         * {@inheritDoc}
         */
        @Override
        protected int translate(final CharSequence input, final int index, final Writer out) throws IOException {
            if (input.charAt(index) == '\\' && index + 1 < input.length() && input.charAt(index + 1) == 'u') {
                // consume optional additional 'u' chars
                int i = 2;
                while (index + i < input.length() && input.charAt(index + i) == 'u') {
                    i++;
                }
                if (index + i < input.length() && input.charAt(index + i) == '+') {
                    i++;
                }
                if (index + i + 4 <= input.length()) {
                    // Get 4 hex digits
                    final CharSequence unicode = input.subSequence(index + i, index + i + 4);
                    try {
                        final int value = Integer.parseInt(unicode.toString(), 16);
                        out.write((char) value);
                    } catch (final NumberFormatException nfe) {
                        throw new IllegalArgumentException("Unable to parse unicode value: " + unicode, nfe);
                    }
                    return i + 4;
                }
                throw new IllegalArgumentException("Less than 4 hex digits in unicode value: '" + input.subSequence(index, input.length()) + "' due to end of CharSequence");
            }
            return 0;
        }
    }
}
