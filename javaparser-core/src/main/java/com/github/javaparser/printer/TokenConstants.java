package com.github.javaparser.printer;

import static com.github.javaparser.GeneratedJavaParserConstants.*;

/**
 * It complements GeneratedJavaParserConstants
 */
public class TokenConstants {
    public static int EOF_TOKEN = 0;
    public static int SPACE_TOKEN = 1;
    public static int SPACE_TOKEN_ALT = 32;
    public static int TAB_TOKEN = 2;
    public static int LINEFEED_TOKEN = 3;
    public static int CARRIAGE_RETURN_TOKEN = 4;

    public static boolean isWhitespace(int tokenType) {
        return tokenType == EOF_TOKEN
                || tokenType == LINEFEED_TOKEN
                || tokenType == CARRIAGE_RETURN_TOKEN
                || tokenType == SPACE_TOKEN
                || tokenType == SPACE_TOKEN_ALT
                || tokenType == TAB_TOKEN;
    }

    public static boolean isEndOfLineCharacter(int tokenType) {
        return tokenType == LINEFEED_TOKEN || tokenType == CARRIAGE_RETURN_TOKEN;
    }

    public static boolean isWhitespaceOrComment(int tokenType) {
        return isWhitespace(tokenType) || isComment(tokenType);
    }

    public static boolean isSpaceOrTab(int tokenType) {
        return tokenType == SPACE_TOKEN || tokenType == TAB_TOKEN || tokenType == SPACE_TOKEN_ALT;
    }

    public static boolean isComment(int tokenType) {
        return tokenType == SINGLE_LINE_COMMENT
                || tokenType == MULTI_LINE_COMMENT
                || tokenType == JAVA_DOC_COMMENT;
    }
}
