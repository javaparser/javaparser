package com.github.javaparser.utils;

import java.util.Optional;

/**
 * A representation of line endings, that can be used throughout the codebase.
 * <br>This is to replace {@code Utils.EOL} which is not explicit in representing the system's EOL character.
 * <br>It also exposes helper methods for, e.g., detection of the line ending of a given string.
 *
 * @author Roger Howell
 * @see <a href="https://github.com/javaparser/javaparser/issues/2647">https://github.com/javaparser/javaparser/issues/2647</a>
 */
public enum LineEnding {
    /**
     * The CR {@code \r} line ending is the default line separator for classic MacOS
     */
    CR("\r"),
    /**
     * The LF {@code \n} line ending is the default line separator for Unix and modern MacOS
     */
    LF("\n"),
    /**
     * The CRLF {@code \r\n} line ending is the default line separator for Windows
     */
    CRLF("\r\n"),
    /**
     * This line ending is set to whatever the host system's line separator is
     */
    SYSTEM(System.getProperty("line.separator")),
    /**
     * The ARBITRARY line ending can be used where we do not care about the line separator,
     * only that we use the same one consistently
     */
    ARBITRARY("\n"),
    /**
     * The MIXED line ending is used where strings appear to have multiple different line separators e.g. {@code "line
     * 1\nline 2\rline 3\r\n"} or {@code "line 1\nline 2\rline 3\nline 4\n"}
     */
    MIXED(""),
    /**
     * The UNKNOWN line ending can be used in the case where the given string has not yet been analysed to determine its
     * line separator
     */
    UNKNOWN(""),
    /**
     * The NONE line ending is used where there are precisely zero line endings e.g. a simple one-line string
     */
    NONE("");

    private final String text;

    LineEnding(String text) {
        this.text = text;
    }

    public boolean isStandardEol() {
        // Compare based on the strings to allow for e.g. LineEnding.SYSTEM
        if (equalsString(LineEnding.CR) ||equalsString(LineEnding.LF) || equalsString(LineEnding.CRLF)) {
            return true;
        }

        return false;
    }

    public String escaped() {
        String result = text
                .replace("\r", "\\r")
                .replace("\n", "\\n");

        return result;
    }

    /**
     * @param ending A string containing ONLY the line separator needle (e.g. {@code \r}, {@code \n}, or {@code \r\n})
     * @return Where the given ending is a "standard" line separator (i.e. {@code \r}, {@code \n}, or {@code \r\n}),
     * return that. Otherwise an empty optional.
     */
    public static Optional<LineEnding> lookup(String ending) {
        if (CR.toString().equals(ending)) {
            return Optional.of(CR);
        } else if (LF.toString().equals(ending)) {
            return Optional.of(LF);
        } else if (CRLF.toString().equals(ending)) {
            return Optional.of(CRLF);
        } else {
            return Optional.empty();
        }
    }

    public static Optional<LineEnding> lookupEscaped(String ending) {
        if (CR.escaped().equals(ending)) {
            return Optional.of(CR);
        } else if (LF.escaped().equals(ending)) {
            return Optional.of(LF);
        } else if (CRLF.escaped().equals(ending)) {
            return Optional.of(CRLF);
        } else {
            return Optional.empty();
        }
    }

    /**
     * @return The number of times that the given needle is found within the haystack.
     */
    private static int count(String haystack, String needle) {
        // Note that if the needle is multiple characters, e.g. \r\n, the difference in string length will be disproportionately affected.
        return (haystack.length() - haystack.replaceAll(needle, "").length()) / needle.length();
    }

    public static LineEnding detect(String string) {
        int countCr = count(string, "\r");
        int countLf = count(string, "\n");
        int countCrLf = count(string, "\r\n");

        boolean noLineEndings = countCr == 0 && countLf == 0 && countCrLf == 0;
        if (noLineEndings) {
            return NONE;
        }

        boolean crOnly = countCr > 0 && countLf == 0 && countCrLf == 0;
        if (crOnly) {
            return CR;
        }
        boolean lfOnly = countCr == 0 && countLf > 0 && countCrLf == 0;
        if (lfOnly) {
            return LF;
        }

        // Note that wherever \r\n are found, there will also be an equal number of \r and \n characters found.
        boolean crLfOnly = countCr == countLf && countLf == countCrLf;
        if (crLfOnly) {
            return CRLF;
        }

        // Not zero line endings, and not a single line ending, thus is mixed.
        return MIXED;
    }

    @Override
    public String toString() {
        return text;
    }

    public boolean equalsString(LineEnding lineEnding) {
        return text.equals(lineEnding.toString());
    }

}
