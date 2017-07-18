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

package com.github.javaparser;

import java.util.List;
import java.util.Optional;

import static com.github.javaparser.GeneratedJavaParserConstants.*;
import static com.github.javaparser.Position.pos;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A token from a parsed source file.
 * (Awkwardly named "Java"Token since JavaCC already generates an internal class Token.)
 */
public class JavaToken {
    public static final JavaToken INVALID = new JavaToken();

    private final Range range;
    private int kind;
    private final String text;
    private final Optional<JavaToken> previousToken;
    private Optional<JavaToken> nextToken = Optional.empty();

    private JavaToken() {
        range = new Range(pos(-1, -1), pos(-1, -1));
        kind = 0;
        text = "INVALID";
        previousToken = Optional.empty();
    }

    public JavaToken(Token token, List<JavaToken> tokens) {
        Range range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.endColumn);
        String text = token.image;

        // You could be puzzled by the following lines
        //
        // The reason why these lines are necessary is the fact that Java is ambiguous. There are cases where the
        // sequence of characters ">>>" and ">>" should be recognized as the single tokens ">>>" and ">>". In other
        // cases however we want to split those characters in single GT tokens (">").
        //
        // For example, in expressions ">>" and ">>>" are valid, while when defining types we could have this:
        //
        //   List<List<Set<String>>>>
        //
        // You can see that the sequence ">>>>" should be interpreted as four consecutive ">" tokens closing a type
        // parameter list.
        //
        // The JavaCC handle this case by first recognizing always the longest token, and then depending on the context
        // putting back the unused chars in the stream. However in those cases the token provided is invalid: it has an
        // image corresponding to the text originally recognized, without considering that after some characters could
        // have been put back into the stream.
        //
        // So in the case of:
        //
        //   List<List<Set<String>>>>
        //                       ___   -> recognized as ">>>", then ">>" put back in the stream but
        //                                Token(type=GT, image=">>>") passed to this class
        //                        ___  -> recognized as ">>>", then ">>" put back in the stream but
        //                                Token(type=GT, image=">>>") passed to this class
        //                         __  -> recognized as ">>", then ">" put back in the stream but
        //                                Token(type=GT, image=">>") passed to this class
        //                          _  -> Token(type=GT, image=">") good!
        //
        // So given the image could be wrong but the type is correct, we look at the type of the token and we fix
        // the image. Everybody is happy and we can keep this horrible thing as our little secret.

        if (token.kind == GeneratedJavaParserConstants.GT) {
            range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.beginColumn);
            text = ">";
        } else if (token.kind == GeneratedJavaParserConstants.RSIGNEDSHIFT) {
            range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.beginColumn + 1);
            text = ">>";
        }
        this.range = range;
        this.kind = token.kind;
        this.text = text;
        if (!tokens.isEmpty()) {
            final JavaToken previousToken = tokens.get(tokens.size() - 1);
            this.previousToken = Optional.of(previousToken);
            previousToken.nextToken = Optional.of(this);
        } else {
            previousToken = Optional.empty();
        }
    }

    public JavaToken(Range range, int kind, String text, Optional<JavaToken> previousToken, Optional<JavaToken> nextToken) {
        this.range = range;
        this.kind = kind;
        this.text = text;
        this.previousToken = previousToken;
        this.nextToken = nextToken;
    }

    public Range getRange() {
        return range;
    }

    public int getKind() {
        return kind;
    }

    void setKind(int kind) {
        this.kind = kind;
    }

    public String getText() {
        return text;
    }

    public Optional<JavaToken> getNextToken() {
        return nextToken;
    }

    public Optional<JavaToken> getPreviousToken() {
        return previousToken;
    }

    @Override
    public String toString() {
        return text;
    }

    public boolean valid() {
        return !invalid();
    }

    public boolean invalid() {
        return this == INVALID;
    }

    public JavaToken orIfInvalid(JavaToken anotherToken) {
        assertNotNull(anotherToken);
        if (valid() || anotherToken.invalid()) {
            return this;
        }
        return anotherToken;
    }

    public enum Category {
        WHITESPACE, COMMENT, IDENTIFIER, KEYWORD, LITERAL, SEPARATOR, OPERATOR
    }

    /**
     * @return a high level category for this token.
     */
    public Category getCategory() {
        switch (kind) {
            case EOF:
            case SPACE:
            case WINDOWS_EOL:
            case TAB:
            case UNIX_EOL:
            case OLD_MAC_EOL:
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
                return Category.WHITESPACE;
            case SINGLE_LINE_COMMENT:
            case JAVA_DOC_COMMENT:
            case MULTI_LINE_COMMENT:
                return Category.COMMENT;
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
            case FALSE:
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
            case NULL:
            case PACKAGE:
            case PRIVATE:
            case PROTECTED:
            case PUBLIC:
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
            case TRUE:
            case TRY:
            case VOID:
            case VOLATILE:
            case WHILE:
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
                return Category.KEYWORD;
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
                return Category.LITERAL;
            case IDENTIFIER:
            case LETTER:
            case PART_LETTER:
                return Category.IDENTIFIER;
            case LPAREN:
            case RPAREN:
            case LBRACE:
            case RBRACE:
            case LBRACKET:
            case RBRACKET:
            case SEMICOLON:
            case COMMA:
            case DOT:
            case AT:
                return Category.SEPARATOR;
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
            case ELLIPSIS:
            case ARROW:
            case DOUBLECOLON:
            case RUNSIGNEDSHIFT:
            case RSIGNEDSHIFT:
            case GT:
                return Category.OPERATOR;
            default:
                throw new AssertionError("Invalid token kind " + kind);
        }
    }
}
