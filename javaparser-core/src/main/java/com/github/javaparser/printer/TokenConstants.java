package com.github.javaparser.printer;

import com.github.javaparser.GeneratedJavaParserConstants;

/**
 * It complements GeneratedJavaParserConstants
 */
public class TokenConstants {
    public static int EOF_TOKEN = 0;
    public static int SPACE_TOKEN = 1;
    public static int TAB_TOKEN = 2;
    public static int NEWLINE_TOKEN = 3;

    public static boolean isWhitespace(int tokenType) {
        return tokenType == EOF_TOKEN
                || tokenType == NEWLINE_TOKEN
                || tokenType == SPACE_TOKEN
                || tokenType == TAB_TOKEN;
    }

    public static boolean isWhitespaceOrComment(int tokenType) {
        return isWhitespace(tokenType) || isComment(tokenType);
    }

    public static boolean isSpaceOrTab(int tokenType) {
        return tokenType == SPACE_TOKEN || tokenType == TAB_TOKEN;
    }

    public static boolean isComment(int tokenType) {
        return tokenType == GeneratedJavaParserConstants.SINGLE_LINE_COMMENT
                || tokenType == GeneratedJavaParserConstants.MULTI_LINE_COMMENT
                || tokenType == GeneratedJavaParserConstants.JAVA_DOC_COMMENT;
    }
}
