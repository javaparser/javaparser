package com.github.javaparser.utils;

import java.util.Optional;

public enum LineEnding {
    CR("\r"),
    LF("\n"),
    CRLF("\r\n"),
    SYSTEM(System.getProperty("line.separator")),
    MIXED(""),
    UNKNOWN(""),
    NONE("");

    private final String text;

    LineEnding(String text) {
        this.text = text;
    }

    public String escaped() {
        return text.replaceAll("\\\\", "\\\\\\\\");
    }

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

    private static int count(String haystack, String needle) {
        return (haystack.length() - haystack.replaceAll(needle, "").length()) / needle.length();
    }

    public static LineEnding detect(String string) {

        int countCr = count(string, "\r");
        int countLf = count(string, "\r");
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
        boolean crLfOnly = countCr == 0 && countLf == 0 && countCrLf > 0;
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

}
