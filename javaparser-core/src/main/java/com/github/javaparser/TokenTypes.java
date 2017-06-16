package com.github.javaparser;

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.utils.Utils.EOL;

/**
 * Complements GeneratedJavaParserConstants
 */
public class TokenTypes {
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
            case TAB:
            case FORM_FEED:
            case NEXT_LINE:
            case NON_BREAKING_SPACE:
            case OGHAM_SPACE:
            case MONGOLIAN_VOWEL_SEPARATOR:
            case EN_QUAD:
            case EM_QUAD:
            case EN_SPACE:
            case EM_SPACE:
            case THREE_PER_EM_SPACE:
            case FOUR_PER_EM_SPACE:
            case SIX_PER_EM_SPACE:
            case FIGURE_SPACE:
            case PUNCTUATION_SPACE:
            case THIN_SPACE:
            case HAIR_SPACE:
            case ZERO_WIDTH_SPACE:
            case ZERO_WIDTH_NON_JOINER:
            case ZERO_WIDTH_JOINER:
            case LINE_SEPARATOR:
            case PARAGRAPH_SEPARATOR:
            case NARROW_NO_BREAK_SPACE:
            case MEDIUM_MATHEMATICAL_SPACE:
            case WORD_JOINER:
            case IDEOGRAPHIC_SPACE:
            case ZERO_WIDTH_NO_BREAK_SPACE:
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
        if (EOL.equals("\n")) {
            return UNIX_EOL;
        }
        if (EOL.equals("\r\n")) {
            return WINDOWS_EOL;
        }
        if (EOL.equals("\r")) {
            return OLD_MAC_EOL;
        }
        throw new AssertionError("Unknown EOL character sequence");
    }

    public static int spaceToken() {
        return SPACE;
    }
}
