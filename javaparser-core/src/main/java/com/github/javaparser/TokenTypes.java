/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2021 The JavaParser Team.
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

import static com.github.javaparser.GeneratedJavaParserConstants.ABSTRACT;
import static com.github.javaparser.GeneratedJavaParserConstants.ANDASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.ARROW;
import static com.github.javaparser.GeneratedJavaParserConstants.ASSERT;
import static com.github.javaparser.GeneratedJavaParserConstants.ASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.AT;
import static com.github.javaparser.GeneratedJavaParserConstants.BANG;
import static com.github.javaparser.GeneratedJavaParserConstants.BINARY_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.BIT_AND;
import static com.github.javaparser.GeneratedJavaParserConstants.BIT_OR;
import static com.github.javaparser.GeneratedJavaParserConstants.BOOLEAN;
import static com.github.javaparser.GeneratedJavaParserConstants.BREAK;
import static com.github.javaparser.GeneratedJavaParserConstants.BYTE;
import static com.github.javaparser.GeneratedJavaParserConstants.CASE;
import static com.github.javaparser.GeneratedJavaParserConstants.CATCH;
import static com.github.javaparser.GeneratedJavaParserConstants.CHAR;
import static com.github.javaparser.GeneratedJavaParserConstants.CHARACTER_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.CLASS;
import static com.github.javaparser.GeneratedJavaParserConstants.COLON;
import static com.github.javaparser.GeneratedJavaParserConstants.COMMA;
import static com.github.javaparser.GeneratedJavaParserConstants.COMMENT_CONTENT;
import static com.github.javaparser.GeneratedJavaParserConstants.CONST;
import static com.github.javaparser.GeneratedJavaParserConstants.CONTINUE;
import static com.github.javaparser.GeneratedJavaParserConstants.CTRL_Z;
import static com.github.javaparser.GeneratedJavaParserConstants.DECIMAL_EXPONENT;
import static com.github.javaparser.GeneratedJavaParserConstants.DECIMAL_FLOATING_POINT_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.DECIMAL_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.DECR;
import static com.github.javaparser.GeneratedJavaParserConstants.DO;
import static com.github.javaparser.GeneratedJavaParserConstants.DOT;
import static com.github.javaparser.GeneratedJavaParserConstants.DOUBLE;
import static com.github.javaparser.GeneratedJavaParserConstants.DOUBLECOLON;
import static com.github.javaparser.GeneratedJavaParserConstants.ELLIPSIS;
import static com.github.javaparser.GeneratedJavaParserConstants.ELSE;
import static com.github.javaparser.GeneratedJavaParserConstants.ENTER_JAVADOC_COMMENT;
import static com.github.javaparser.GeneratedJavaParserConstants.ENTER_MULTILINE_COMMENT;
import static com.github.javaparser.GeneratedJavaParserConstants.ENTER_TEXT_BLOCK;
import static com.github.javaparser.GeneratedJavaParserConstants.ENUM;
import static com.github.javaparser.GeneratedJavaParserConstants.EOF;
import static com.github.javaparser.GeneratedJavaParserConstants.EQ;
import static com.github.javaparser.GeneratedJavaParserConstants.EXPORTS;
import static com.github.javaparser.GeneratedJavaParserConstants.EXTENDS;
import static com.github.javaparser.GeneratedJavaParserConstants.FALSE;
import static com.github.javaparser.GeneratedJavaParserConstants.FINAL;
import static com.github.javaparser.GeneratedJavaParserConstants.FINALLY;
import static com.github.javaparser.GeneratedJavaParserConstants.FLOAT;
import static com.github.javaparser.GeneratedJavaParserConstants.FLOATING_POINT_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.FOR;
import static com.github.javaparser.GeneratedJavaParserConstants.GE;
import static com.github.javaparser.GeneratedJavaParserConstants.GOTO;
import static com.github.javaparser.GeneratedJavaParserConstants.GT;
import static com.github.javaparser.GeneratedJavaParserConstants.HEXADECIMAL_EXPONENT;
import static com.github.javaparser.GeneratedJavaParserConstants.HEXADECIMAL_FLOATING_POINT_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.HEX_DIGITS;
import static com.github.javaparser.GeneratedJavaParserConstants.HEX_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.HOOK;
import static com.github.javaparser.GeneratedJavaParserConstants.IDENTIFIER;
import static com.github.javaparser.GeneratedJavaParserConstants.IF;
import static com.github.javaparser.GeneratedJavaParserConstants.IMPLEMENTS;
import static com.github.javaparser.GeneratedJavaParserConstants.IMPORT;
import static com.github.javaparser.GeneratedJavaParserConstants.INCR;
import static com.github.javaparser.GeneratedJavaParserConstants.INSTANCEOF;
import static com.github.javaparser.GeneratedJavaParserConstants.INT;
import static com.github.javaparser.GeneratedJavaParserConstants.INTEGER_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.INTERFACE;
import static com.github.javaparser.GeneratedJavaParserConstants.JAVADOC_COMMENT;
import static com.github.javaparser.GeneratedJavaParserConstants.LBRACE;
import static com.github.javaparser.GeneratedJavaParserConstants.LBRACKET;
import static com.github.javaparser.GeneratedJavaParserConstants.LE;
import static com.github.javaparser.GeneratedJavaParserConstants.LETTER;
import static com.github.javaparser.GeneratedJavaParserConstants.LONG;
import static com.github.javaparser.GeneratedJavaParserConstants.LONG_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.LPAREN;
import static com.github.javaparser.GeneratedJavaParserConstants.LSHIFT;
import static com.github.javaparser.GeneratedJavaParserConstants.LSHIFTASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.LT;
import static com.github.javaparser.GeneratedJavaParserConstants.MINUS;
import static com.github.javaparser.GeneratedJavaParserConstants.MINUSASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.MODULE;
import static com.github.javaparser.GeneratedJavaParserConstants.MULTI_LINE_COMMENT;
import static com.github.javaparser.GeneratedJavaParserConstants.NATIVE;
import static com.github.javaparser.GeneratedJavaParserConstants.NE;
import static com.github.javaparser.GeneratedJavaParserConstants.NEW;
import static com.github.javaparser.GeneratedJavaParserConstants.NULL;
import static com.github.javaparser.GeneratedJavaParserConstants.OCTAL_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.OLD_MAC_EOL;
import static com.github.javaparser.GeneratedJavaParserConstants.OPEN;
import static com.github.javaparser.GeneratedJavaParserConstants.OPENS;
import static com.github.javaparser.GeneratedJavaParserConstants.ORASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.PACKAGE;
import static com.github.javaparser.GeneratedJavaParserConstants.PART_LETTER;
import static com.github.javaparser.GeneratedJavaParserConstants.PLUS;
import static com.github.javaparser.GeneratedJavaParserConstants.PLUSASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.PRIVATE;
import static com.github.javaparser.GeneratedJavaParserConstants.PROTECTED;
import static com.github.javaparser.GeneratedJavaParserConstants.PROVIDES;
import static com.github.javaparser.GeneratedJavaParserConstants.PUBLIC;
import static com.github.javaparser.GeneratedJavaParserConstants.RBRACE;
import static com.github.javaparser.GeneratedJavaParserConstants.RBRACKET;
import static com.github.javaparser.GeneratedJavaParserConstants.RECORD;
import static com.github.javaparser.GeneratedJavaParserConstants.REM;
import static com.github.javaparser.GeneratedJavaParserConstants.REMASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.REQUIRES;
import static com.github.javaparser.GeneratedJavaParserConstants.RETURN;
import static com.github.javaparser.GeneratedJavaParserConstants.RPAREN;
import static com.github.javaparser.GeneratedJavaParserConstants.RSIGNEDSHIFT;
import static com.github.javaparser.GeneratedJavaParserConstants.RSIGNEDSHIFTASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.RUNSIGNEDSHIFT;
import static com.github.javaparser.GeneratedJavaParserConstants.RUNSIGNEDSHIFTASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.SC_AND;
import static com.github.javaparser.GeneratedJavaParserConstants.SC_OR;
import static com.github.javaparser.GeneratedJavaParserConstants.SEMICOLON;
import static com.github.javaparser.GeneratedJavaParserConstants.SHORT;
import static com.github.javaparser.GeneratedJavaParserConstants.SINGLE_LINE_COMMENT;
import static com.github.javaparser.GeneratedJavaParserConstants.SLASH;
import static com.github.javaparser.GeneratedJavaParserConstants.SLASHASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.SPACE;
import static com.github.javaparser.GeneratedJavaParserConstants.STAR;
import static com.github.javaparser.GeneratedJavaParserConstants.STARASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.STATIC;
import static com.github.javaparser.GeneratedJavaParserConstants.STRICTFP;
import static com.github.javaparser.GeneratedJavaParserConstants.STRING_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.SUPER;
import static com.github.javaparser.GeneratedJavaParserConstants.SWITCH;
import static com.github.javaparser.GeneratedJavaParserConstants.SYNCHRONIZED;
import static com.github.javaparser.GeneratedJavaParserConstants.TEXT_BLOCK_CONTENT;
import static com.github.javaparser.GeneratedJavaParserConstants.TEXT_BLOCK_LITERAL;
import static com.github.javaparser.GeneratedJavaParserConstants.THIS;
import static com.github.javaparser.GeneratedJavaParserConstants.THROW;
import static com.github.javaparser.GeneratedJavaParserConstants.THROWS;
import static com.github.javaparser.GeneratedJavaParserConstants.TILDE;
import static com.github.javaparser.GeneratedJavaParserConstants.TO;
import static com.github.javaparser.GeneratedJavaParserConstants.TRANSIENT;
import static com.github.javaparser.GeneratedJavaParserConstants.TRANSITIVE;
import static com.github.javaparser.GeneratedJavaParserConstants.TRUE;
import static com.github.javaparser.GeneratedJavaParserConstants.TRY;
import static com.github.javaparser.GeneratedJavaParserConstants.UNICODE_ESCAPE;
import static com.github.javaparser.GeneratedJavaParserConstants.UNIX_EOL;
import static com.github.javaparser.GeneratedJavaParserConstants.USES;
import static com.github.javaparser.GeneratedJavaParserConstants.VOID;
import static com.github.javaparser.GeneratedJavaParserConstants.VOLATILE;
import static com.github.javaparser.GeneratedJavaParserConstants.WHILE;
import static com.github.javaparser.GeneratedJavaParserConstants.WINDOWS_EOL;
import static com.github.javaparser.GeneratedJavaParserConstants.WITH;
import static com.github.javaparser.GeneratedJavaParserConstants.XOR;
import static com.github.javaparser.GeneratedJavaParserConstants.XORASSIGN;
import static com.github.javaparser.GeneratedJavaParserConstants.YIELD;
import static com.github.javaparser.GeneratedJavaParserConstants._DEFAULT;

/**
 * Complements GeneratedJavaParserConstants
 */
public class TokenTypes {

    private TokenTypes() {
        // Private constructor to prevent initialisation.
    }

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
        switch (kind) {
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
