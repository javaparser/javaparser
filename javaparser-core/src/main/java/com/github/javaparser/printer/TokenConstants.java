package com.github.javaparser.printer;

import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.utils.Utils;

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.utils.Utils.*;

/**
 * It complements GeneratedJavaParserConstants
 */
public class TokenConstants {
    public static boolean isWhitespace(int tokenType) {
        return tokenType >= EOF && tokenType <= ZERO_WIDTH_NO_BREAK_SPACE;
    }

    public static boolean isEndOfLineCharacter(int tokenType) {
        switch (tokenType) {
            case WINDOWS_EOL:
            case OLD_MAC_EOL:
            case UNIX_EOL:
                return true;
            default:
                return false;
        }
    }

    public static boolean isWhitespaceOrComment(int tokenType) {
        return isWhitespace(tokenType) || isComment(tokenType);
    }

    public static boolean isSpaceOrTab(int tokenType) {
        switch (tokenType) {
            case SPACE:
                // TODO lots more space tokens in the grammar!
            case GeneratedJavaParserConstants.TAB:
                return true;
            default:
                return false;
        }
    }

    public static boolean isComment(int tokenType) {
        return tokenType == SINGLE_LINE_COMMENT
                || tokenType == MULTI_LINE_COMMENT
                || tokenType == JAVA_DOC_COMMENT;
    }

    public static int eolToken() {
        if(EOL.equals("\n")){
            return UNIX_EOL;
        }
        if(EOL.equals("\r\n")){
            return WINDOWS_EOL;
        }
        if(EOL.equals("\r")){
            return OLD_MAC_EOL;
        }
        throw new AssertionError("Unknown EOL character sequence");
    }

    public static int spaceToken() {
        return SPACE;
    }
}
