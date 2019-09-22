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
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.EOL;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Generated;

/**
 * A token from a parsed source file.
 * (Awkwardly named "Java"Token since JavaCC already generates an internal class Token.)
 * It is a node in a double linked list called token list.
 */
public class JavaToken {

    public static final JavaToken INVALID = new JavaToken();

    private Range range;

    private int kind;

    private String text;

    private JavaToken previousToken = null;

    private JavaToken nextToken = null;

    private JavaToken() {
        this(null, 0, "INVALID", null, null);
    }

    public JavaToken(int kind, String text) {
        this(null, kind, text, null, null);
    }

    JavaToken(Token token, List<JavaToken> tokens) {
        // You could be puzzled by the following lines
        // 
        // The reason why these lines are necessary is the fact that Java is ambiguous. There are cases where the
        // sequence of characters ">>>" and ">>" should be recognized as the single tokens ">>>" and ">>". In other
        // cases however we want to split those characters in single GT tokens (">").
        // 
        // For example, in expressions ">>" and ">>>" are valid, while when defining types we could have this:
        // 
        // List<List<Set<String>>>>
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
        // List<List<Set<String>>>>
        // ___   -> recognized as ">>>", then ">>" put back in the stream but Token(type=GT, image=">>>") passed to this class
        // ___  -> recognized as ">>>", then ">>" put back in the stream but Token(type=GT, image=">>>") passed to this class
        // __  -> recognized as ">>", then ">" put back in the stream but Token(type=GT, image=">>") passed to this class
        // _  -> Token(type=GT, image=">") good!
        // 
        // So given the image could be wrong but the type is correct, we look at the type of the token and we fix
        // the image. Everybody is happy and we can keep this horrible thing as our little secret.
        Range range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.endColumn);
        String text = token.image;
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
            this.previousToken = previousToken;
            previousToken.nextToken = this;
        } else {
            previousToken = null;
        }
    }

    /**
     * Create a token of a certain kind.
     */
    public JavaToken(int kind) {
        String content = GeneratedJavaParserConstants.tokenImage[kind];
        if (content.startsWith("\"")) {
            content = content.substring(1, content.length() - 1);
        }
        if (TokenTypes.isEndOfLineToken(kind)) {
            content = EOL;
        } else if (TokenTypes.isWhitespace(kind)) {
            content = " ";
        }
        this.kind = kind;
        this.text = content;
    }

    public JavaToken(Range range, int kind, String text, JavaToken previousToken, JavaToken nextToken) {
        assertNotNull(text);
        this.range = range;
        this.kind = kind;
        this.text = text;
        this.previousToken = previousToken;
        this.nextToken = nextToken;
    }

    public Optional<Range> getRange() {
        return Optional.ofNullable(range);
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
        return Optional.ofNullable(nextToken);
    }

    public Optional<JavaToken> getPreviousToken() {
        return Optional.ofNullable(previousToken);
    }

    public void setRange(Range range) {
        this.range = range;
    }

    public void setText(String text) {
        this.text = text;
    }

    public String asString() {
        return text;
    }

    /**
     * @return the token range that goes from the beginning to the end of the token list this token is a part of.
     */
    public TokenRange toTokenRange() {
        return new TokenRange(findFirstToken(), findLastToken());
    }

    @Override
    public String toString() {
        String text = getText().replace("\n", "\\n").replace("\r", "\\r").replace("\r\n", "\\r\\n").replace("\t", "\\t");
        return f("\"%s\"   <%s>   %s", text, getKind(), getRange().map(Range::toString).orElse("(?)-(?)"));
    }

    /**
     * Used by the parser while constructing nodes. No tokens should be invalid when the parser is done.
     */
    public boolean valid() {
        return !invalid();
    }

    /**
     * Used by the parser while constructing nodes. No tokens should be invalid when the parser is done.
     */
    public boolean invalid() {
        return this == INVALID;
    }

    public enum Category {

        WHITESPACE_NO_EOL,
        EOL,
        COMMENT,
        IDENTIFIER,
        KEYWORD,
        LITERAL,
        SEPARATOR,
        OPERATOR;

        public boolean isWhitespaceOrComment() {
            return isWhitespace() || this == COMMENT;
        }

        public boolean isWhitespace() {
            return this == WHITESPACE_NO_EOL || this == EOL;
        }

        public boolean isEndOfLine() {
            return this == EOL;
        }

        public boolean isComment() {
            return this == COMMENT;
        }

        public boolean isWhitespaceButNotEndOfLine() {
            return this == WHITESPACE_NO_EOL;
        }

        public boolean isIdentifier() {
            return this == IDENTIFIER;
        }

        public boolean isKeyword() {
            return this == KEYWORD;
        }

        public boolean isLiteral() {
            return this == LITERAL;
        }

        public boolean isSeparator() {
            return this == SEPARATOR;
        }

        public boolean isOperator() {
            return this == OPERATOR;
        }
    }

    @Generated("com.github.javaparser.generator.core.other.TokenKindGenerator")
    public enum Kind {

        EOF(0),
        SPACE(1),
        WINDOWS_EOL(2),
        UNIX_EOL(3),
        OLD_MAC_EOL(4),
        SINGLE_LINE_COMMENT(5),
        ENTER_JAVADOC_COMMENT(6),
        ENTER_MULTILINE_COMMENT(7),
        JAVADOC_COMMENT(8),
        MULTI_LINE_COMMENT(9),
        COMMENT_CONTENT(10),
        ABSTRACT(11),
        ASSERT(12),
        BOOLEAN(13),
        BREAK(14),
        BYTE(15),
        CASE(16),
        CATCH(17),
        CHAR(18),
        CLASS(19),
        CONST(20),
        CONTINUE(21),
        _DEFAULT(22),
        DO(23),
        DOUBLE(24),
        ELSE(25),
        ENUM(26),
        EXTENDS(27),
        FALSE(28),
        FINAL(29),
        FINALLY(30),
        FLOAT(31),
        FOR(32),
        GOTO(33),
        IF(34),
        IMPLEMENTS(35),
        IMPORT(36),
        INSTANCEOF(37),
        INT(38),
        INTERFACE(39),
        LONG(40),
        NATIVE(41),
        NEW(42),
        NULL(43),
        PACKAGE(44),
        PRIVATE(45),
        PROTECTED(46),
        PUBLIC(47),
        RETURN(48),
        SHORT(49),
        STATIC(50),
        STRICTFP(51),
        SUPER(52),
        SWITCH(53),
        SYNCHRONIZED(54),
        THIS(55),
        THROW(56),
        THROWS(57),
        TRANSIENT(58),
        TRUE(59),
        TRY(60),
        VOID(61),
        VOLATILE(62),
        WHILE(63),
        YIELD(64),
        REQUIRES(65),
        TO(66),
        WITH(67),
        OPEN(68),
        OPENS(69),
        USES(70),
        MODULE(71),
        EXPORTS(72),
        PROVIDES(73),
        TRANSITIVE(74),
        LONG_LITERAL(75),
        INTEGER_LITERAL(76),
        DECIMAL_LITERAL(77),
        HEX_LITERAL(78),
        OCTAL_LITERAL(79),
        BINARY_LITERAL(80),
        FLOATING_POINT_LITERAL(81),
        DECIMAL_FLOATING_POINT_LITERAL(82),
        DECIMAL_EXPONENT(83),
        HEXADECIMAL_FLOATING_POINT_LITERAL(84),
        HEXADECIMAL_EXPONENT(85),
        HEX_DIGITS(86),
        UNICODE_ESCAPE(87),
        CHARACTER_LITERAL(88),
        STRING_LITERAL(89),
        ENTER_TEXT_BLOCK(90),
        TEXT_BLOCK_LITERAL(91),
        TEXT_BLOCK_CONTENT(92),
        IDENTIFIER(93),
        LETTER(94),
        PART_LETTER(95),
        LPAREN(96),
        RPAREN(97),
        LBRACE(98),
        RBRACE(99),
        LBRACKET(100),
        RBRACKET(101),
        SEMICOLON(102),
        COMMA(103),
        DOT(104),
        AT(105),
        ASSIGN(106),
        LT(107),
        BANG(108),
        TILDE(109),
        HOOK(110),
        COLON(111),
        EQ(112),
        LE(113),
        GE(114),
        NE(115),
        SC_OR(116),
        SC_AND(117),
        INCR(118),
        DECR(119),
        PLUS(120),
        MINUS(121),
        STAR(122),
        SLASH(123),
        BIT_AND(124),
        BIT_OR(125),
        XOR(126),
        REM(127),
        LSHIFT(128),
        PLUSASSIGN(129),
        MINUSASSIGN(130),
        STARASSIGN(131),
        SLASHASSIGN(132),
        ANDASSIGN(133),
        ORASSIGN(134),
        XORASSIGN(135),
        REMASSIGN(136),
        LSHIFTASSIGN(137),
        RSIGNEDSHIFTASSIGN(138),
        RUNSIGNEDSHIFTASSIGN(139),
        ELLIPSIS(140),
        ARROW(141),
        DOUBLECOLON(142),
        RUNSIGNEDSHIFT(143),
        RSIGNEDSHIFT(144),
        GT(145),
        CTRL_Z(146);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 146:
                    return CTRL_Z;
                case 145:
                    return GT;
                case 144:
                    return RSIGNEDSHIFT;
                case 143:
                    return RUNSIGNEDSHIFT;
                case 142:
                    return DOUBLECOLON;
                case 141:
                    return ARROW;
                case 140:
                    return ELLIPSIS;
                case 139:
                    return RUNSIGNEDSHIFTASSIGN;
                case 138:
                    return RSIGNEDSHIFTASSIGN;
                case 137:
                    return LSHIFTASSIGN;
                case 136:
                    return REMASSIGN;
                case 135:
                    return XORASSIGN;
                case 134:
                    return ORASSIGN;
                case 133:
                    return ANDASSIGN;
                case 132:
                    return SLASHASSIGN;
                case 131:
                    return STARASSIGN;
                case 130:
                    return MINUSASSIGN;
                case 129:
                    return PLUSASSIGN;
                case 128:
                    return LSHIFT;
                case 127:
                    return REM;
                case 126:
                    return XOR;
                case 125:
                    return BIT_OR;
                case 124:
                    return BIT_AND;
                case 123:
                    return SLASH;
                case 122:
                    return STAR;
                case 121:
                    return MINUS;
                case 120:
                    return PLUS;
                case 119:
                    return DECR;
                case 118:
                    return INCR;
                case 117:
                    return SC_AND;
                case 116:
                    return SC_OR;
                case 115:
                    return NE;
                case 114:
                    return GE;
                case 113:
                    return LE;
                case 112:
                    return EQ;
                case 111:
                    return COLON;
                case 110:
                    return HOOK;
                case 109:
                    return TILDE;
                case 108:
                    return BANG;
                case 107:
                    return LT;
                case 106:
                    return ASSIGN;
                case 105:
                    return AT;
                case 104:
                    return DOT;
                case 103:
                    return COMMA;
                case 102:
                    return SEMICOLON;
                case 101:
                    return RBRACKET;
                case 100:
                    return LBRACKET;
                case 99:
                    return RBRACE;
                case 98:
                    return LBRACE;
                case 97:
                    return RPAREN;
                case 96:
                    return LPAREN;
                case 95:
                    return PART_LETTER;
                case 94:
                    return LETTER;
                case 93:
                    return IDENTIFIER;
                case 92:
                    return TEXT_BLOCK_CONTENT;
                case 91:
                    return TEXT_BLOCK_LITERAL;
                case 90:
                    return ENTER_TEXT_BLOCK;
                case 89:
                    return STRING_LITERAL;
                case 88:
                    return CHARACTER_LITERAL;
                case 87:
                    return UNICODE_ESCAPE;
                case 86:
                    return HEX_DIGITS;
                case 85:
                    return HEXADECIMAL_EXPONENT;
                case 84:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 83:
                    return DECIMAL_EXPONENT;
                case 82:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 81:
                    return FLOATING_POINT_LITERAL;
                case 80:
                    return BINARY_LITERAL;
                case 79:
                    return OCTAL_LITERAL;
                case 78:
                    return HEX_LITERAL;
                case 77:
                    return DECIMAL_LITERAL;
                case 76:
                    return INTEGER_LITERAL;
                case 75:
                    return LONG_LITERAL;
                case 74:
                    return TRANSITIVE;
                case 73:
                    return PROVIDES;
                case 72:
                    return EXPORTS;
                case 71:
                    return MODULE;
                case 70:
                    return USES;
                case 69:
                    return OPENS;
                case 68:
                    return OPEN;
                case 67:
                    return WITH;
                case 66:
                    return TO;
                case 65:
                    return REQUIRES;
                case 64:
                    return YIELD;
                case 63:
                    return WHILE;
                case 62:
                    return VOLATILE;
                case 61:
                    return VOID;
                case 60:
                    return TRY;
                case 59:
                    return TRUE;
                case 58:
                    return TRANSIENT;
                case 57:
                    return THROWS;
                case 56:
                    return THROW;
                case 55:
                    return THIS;
                case 54:
                    return SYNCHRONIZED;
                case 53:
                    return SWITCH;
                case 52:
                    return SUPER;
                case 51:
                    return STRICTFP;
                case 50:
                    return STATIC;
                case 49:
                    return SHORT;
                case 48:
                    return RETURN;
                case 47:
                    return PUBLIC;
                case 46:
                    return PROTECTED;
                case 45:
                    return PRIVATE;
                case 44:
                    return PACKAGE;
                case 43:
                    return NULL;
                case 42:
                    return NEW;
                case 41:
                    return NATIVE;
                case 40:
                    return LONG;
                case 39:
                    return INTERFACE;
                case 38:
                    return INT;
                case 37:
                    return INSTANCEOF;
                case 36:
                    return IMPORT;
                case 35:
                    return IMPLEMENTS;
                case 34:
                    return IF;
                case 33:
                    return GOTO;
                case 32:
                    return FOR;
                case 31:
                    return FLOAT;
                case 30:
                    return FINALLY;
                case 29:
                    return FINAL;
                case 28:
                    return FALSE;
                case 27:
                    return EXTENDS;
                case 26:
                    return ENUM;
                case 25:
                    return ELSE;
                case 24:
                    return DOUBLE;
                case 23:
                    return DO;
                case 22:
                    return _DEFAULT;
                case 21:
                    return CONTINUE;
                case 20:
                    return CONST;
                case 19:
                    return CLASS;
                case 18:
                    return CHAR;
                case 17:
                    return CATCH;
                case 16:
                    return CASE;
                case 15:
                    return BYTE;
                case 14:
                    return BREAK;
                case 13:
                    return BOOLEAN;
                case 12:
                    return ASSERT;
                case 11:
                    return ABSTRACT;
                case 10:
                    return COMMENT_CONTENT;
                case 9:
                    return MULTI_LINE_COMMENT;
                case 8:
                    return JAVADOC_COMMENT;
                case 7:
                    return ENTER_MULTILINE_COMMENT;
                case 6:
                    return ENTER_JAVADOC_COMMENT;
                case 5:
                    return SINGLE_LINE_COMMENT;
                case 4:
                    return OLD_MAC_EOL;
                case 3:
                    return UNIX_EOL;
                case 2:
                    return WINDOWS_EOL;
                case 1:
                    return SPACE;
                case 0:
                    return EOF;
                default:
                    throw new IllegalArgumentException(f("Token kind %i is unknown.", kind));
            }
        }

        public boolean isPrimitive() {
            return this == BYTE || this == CHAR || this == SHORT || this == INT || this == LONG || this == FLOAT || this == DOUBLE;
        }

        public int getKind() {
            return kind;
        }
    }

    public JavaToken.Category getCategory() {
        return TokenTypes.getCategory(kind);
    }

    /**
     * Inserts newToken into the token list just before this token.
     */
    public void insert(JavaToken newToken) {
        assertNotNull(newToken);
        getPreviousToken().ifPresent(p -> {
            p.nextToken = newToken;
            newToken.previousToken = p;
        });
        previousToken = newToken;
        newToken.nextToken = this;
    }

    /**
     * Inserts newToken into the token list just after this token.
     */
    public void insertAfter(JavaToken newToken) {
        assertNotNull(newToken);
        getNextToken().ifPresent(n -> {
            n.previousToken = newToken;
            newToken.nextToken = n;
        });
        nextToken = newToken;
        newToken.previousToken = this;
    }

    /**
     * Links the tokens around the current token together, making the current token disappear from the list.
     */
    public void deleteToken() {
        final Optional<JavaToken> nextToken = getNextToken();
        final Optional<JavaToken> previousToken = getPreviousToken();
        previousToken.ifPresent(p -> p.nextToken = nextToken.orElse(null));
        nextToken.ifPresent(n -> n.previousToken = previousToken.orElse(null));
    }

    /**
     * Replaces the current token with newToken.
     */
    public void replaceToken(JavaToken newToken) {
        assertNotNull(newToken);
        getPreviousToken().ifPresent(p -> {
            p.nextToken = newToken;
            newToken.previousToken = p;
        });
        getNextToken().ifPresent(n -> {
            n.previousToken = newToken;
            newToken.nextToken = n;
        });
    }

    /**
     * @return the last token in the token list.
     */
    public JavaToken findLastToken() {
        JavaToken current = this;
        while (current.getNextToken().isPresent()) {
            current = current.getNextToken().get();
        }
        return current;
    }

    /**
     * @return the first token in the token list.
     */
    public JavaToken findFirstToken() {
        JavaToken current = this;
        while (current.getPreviousToken().isPresent()) {
            current = current.getPreviousToken().get();
        }
        return current;
    }

    @Override
    public int hashCode() {
        int result = kind;
        result = 31 * result + text.hashCode();
        return result;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        JavaToken javaToken = (JavaToken) o;
        if (kind != javaToken.kind)
            return false;
        if (!text.equals(javaToken.text))
            return false;
        return true;
    }
}
