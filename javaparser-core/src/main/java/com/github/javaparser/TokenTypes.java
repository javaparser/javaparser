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
package com.github.javaparser;

import com.github.javaparser.utils.LineSeparator;

import static com.github.javaparser.GeneratedJavaParserConstants.*;

/**
 * Complements GeneratedJavaParserConstants
 */
public class TokenTypes {

    public static boolean isWhitespace(int kind) {
        return getCategory(kind).isWhitespace();
    }

    public static boolean isEndOfLineToken(int kind) {
        return getCategory(kind).isEndOfLine();
    }

    public static boolean isWhitespaceOrComment(int kind) {
        return getCategory(kind).isWhitespaceOrComment();
    }

    /**
     * @deprecated Use {@link #isWhitespaceButNotEndOfLine(int)} which more explicitly reflects that this also includes
     *  other whitespace e.g. {@code EOF} and {@code CTRL_Z} and a large number of other characters.
     *  See the grammar for details of exactly which characters are included as a "space" (.
     *  <pre>{@code
     *   <SPACE: [" ", "\t", "\f", "\u0085", "\u00A0", "\u1680", "\u180e", "\u2000", "\u2001", "\u2002", "\u2003", "\u2004", "\u2005",
     *       "\u2006", "\u2007", "\u2008", "\u2009", "\u200a", "\u200b", "\u200c", "\u200d", "\u2028", "\u2029", "\u202f", "\u205f", "\u2060", "\u3000", "\ufeff"]>
     *  }</pre>
     */
    @Deprecated
    public static boolean isSpaceOrTab(int kind) {
        return isWhitespaceButNotEndOfLine(kind);
    }

    public static boolean isWhitespaceButNotEndOfLine(int kind) {
        return getCategory(kind).isWhitespaceButNotEndOfLine();
    }

    public static boolean isComment(int kind) {
        return getCategory(kind).isComment();
    }

    /**
     * @return the kind of EOL token to use on the platform you're running on.
     */
    public static int eolTokenKind(LineSeparator lineSeparator) {
        if (lineSeparator.equalsString(LineSeparator.LF)) {
            return UNIX_EOL;
        }
        if (lineSeparator.equalsString(LineSeparator.CRLF)) {
            return WINDOWS_EOL;
        }
        if (lineSeparator.equalsString(LineSeparator.CR)) {
            return OLD_MAC_EOL;
        }
        throw new AssertionError("Unknown EOL character sequence");
    }

    public static int eolTokenKind() {
        return eolTokenKind(LineSeparator.SYSTEM);
    }

    /**
     * @return the token kind for a single space.
     */
    public static int spaceTokenKind() {
        return SPACE;
    }

    /**
     * Category of a token, a little more detailed than
     * <a href="https://docs.oracle.com/javase/specs/jls/se8/html/jls-3.html#jls-3.5">The JLS</a>.
     */
    public static JavaToken.Category getCategory(int kind) {
        switch(kind) {
            case WINDOWS_EOL:
            case UNIX_EOL:
            case OLD_MAC_EOL:
                return JavaToken.Category.EOL;
            case EOF:
            case SPACE:
            case CTRL_Z:
                return JavaToken.Category.WHITESPACE_NO_EOL;
            case SINGLE_LINE_COMMENT:
            case JAVADOC_COMMENT:
            case MULTI_LINE_COMMENT:
                return JavaToken.Category.COMMENT;
            case ABSTRACT:
            case ASSERT:
            case BOOLEAN:
            case BREAK:
            case BYTE:
            case CASE:
            case CATCH:
            case CHAR:
            case CLASS:
            case CONST:
            case CONTINUE:
            case _DEFAULT:
            case DO:
            case DOUBLE:
            case ELSE:
            case ENUM:
            case EXTENDS:
            case FINAL:
            case FINALLY:
            case FLOAT:
            case FOR:
            case GOTO:
            case IF:
            case IMPLEMENTS:
            case IMPORT:
            case INSTANCEOF:
            case INT:
            case INTERFACE:
            case LONG:
            case NATIVE:
            case NEW:
            case PACKAGE:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
            case RECORD:
            case RETURN:
            case SHORT:
            case STATIC:
            case STRICTFP:
            case SUPER:
            case SWITCH:
            case SYNCHRONIZED:
            case THIS:
            case THROW:
            case THROWS:
            case TRANSIENT:
            case TRY:
            case VOID:
            case VOLATILE:
            case WHILE:
            case YIELD:
            case REQUIRES:
            case TO:
            case WITH:
            case OPEN:
            case OPENS:
            case USES:
            case MODULE:
            case EXPORTS:
            case PROVIDES:
            case TRANSITIVE:
                return JavaToken.Category.KEYWORD;
            case LONG_LITERAL:
            case INTEGER_LITERAL:
            case DECIMAL_LITERAL:
            case HEX_LITERAL:
            case OCTAL_LITERAL:
            case BINARY_LITERAL:
            case FLOATING_POINT_LITERAL:
            case DECIMAL_FLOATING_POINT_LITERAL:
            case DECIMAL_EXPONENT:
            case HEXADECIMAL_FLOATING_POINT_LITERAL:
            case HEXADECIMAL_EXPONENT:
            case CHARACTER_LITERAL:
            case STRING_LITERAL:
            case TEXT_BLOCK_LITERAL:
            case TRUE:
            case FALSE:
            case NULL:
                return JavaToken.Category.LITERAL;
            case IDENTIFIER:
                return JavaToken.Category.IDENTIFIER;
            case LPAREN:
            case RPAREN:
            case LBRACE:
            case RBRACE:
            case LBRACKET:
            case RBRACKET:
            case SEMICOLON:
            case COMMA:
            case DOT:
            case ELLIPSIS:
            case AT:
            case DOUBLECOLON:
                return JavaToken.Category.SEPARATOR;
            case ASSIGN:
            case LT:
            case BANG:
            case TILDE:
            case HOOK:
            case COLON:
            case EQ:
            case LE:
            case GE:
            case NE:
            case SC_OR:
            case SC_AND:
            case INCR:
            case DECR:
            case PLUS:
            case MINUS:
            case STAR:
            case SLASH:
            case BIT_AND:
            case BIT_OR:
            case XOR:
            case REM:
            case LSHIFT:
            case PLUSASSIGN:
            case MINUSASSIGN:
            case STARASSIGN:
            case SLASHASSIGN:
            case ANDASSIGN:
            case ORASSIGN:
            case XORASSIGN:
            case REMASSIGN:
            case LSHIFTASSIGN:
            case RSIGNEDSHIFTASSIGN:
            case RUNSIGNEDSHIFTASSIGN:
            case ARROW:
            case RUNSIGNEDSHIFT:
            case RSIGNEDSHIFT:
            case GT:
                return JavaToken.Category.OPERATOR;
            // The following are tokens that are only used internally by the lexer
            case ENTER_JAVADOC_COMMENT:
            case ENTER_MULTILINE_COMMENT:
            case COMMENT_CONTENT:
            case HEX_DIGITS:
            case LETTER:
            case UNICODE_ESCAPE:
            case PART_LETTER:
            case TEXT_BLOCK_CONTENT:
            case ENTER_TEXT_BLOCK:
            default:
                throw new AssertionError("Unable to categorise token kind " + kind + " -- has it recently been added to the grammar but not classified within TokenTypes.java, perhaps?");
        }
    }
}
