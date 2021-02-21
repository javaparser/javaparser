/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2020 The JavaParser Team.
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

import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static com.github.javaparser.utils.Utils.assertNotNull;
import java.util.List;
import java.util.Optional;
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
            content = SYSTEM_EOL;
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

    /*
     * Returns true if the token has a range
     */
    public boolean hasRange() {
        return getRange().isPresent();
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
        SINGLE_LINE_JML(5),
        SINGLE_LINE_COMMENT(6),
        ENTER_JAVADOC_COMMENT(7),
        ENTER_MULTILINE_JML(8),
        ENTER_MULTILINE_COMMENT(9),
        JAVADOC_COMMENT(10),
        MULTI_LINE_COMMENT(11),
        COMMENT_CONTENT(12),
        ABSTRACT(13),
        ASSERT(14),
        BOOLEAN(15),
        BREAK(16),
        BYTE(17),
        CASE(18),
        CATCH(19),
        CHAR(20),
        CLASS(21),
        CONST(22),
        CONTINUE(23),
        _DEFAULT(24),
        DO(25),
        DOUBLE(26),
        ELSE(27),
        ENUM(28),
        EXTENDS(29),
        FALSE(30),
        FINAL(31),
        FINALLY(32),
        FLOAT(33),
        FOR(34),
        GOTO(35),
        IF(36),
        IMPLEMENTS(37),
        IMPORT(38),
        INSTANCEOF(39),
        INT(40),
        INTERFACE(41),
        LONG(42),
        NATIVE(43),
        NEW(44),
        NULL(45),
        PACKAGE(46),
        PRIVATE(47),
        PROTECTED(48),
        PUBLIC(49),
        RETURN(50),
        SHORT(51),
        STATIC(52),
        STRICTFP(53),
        SUPER(54),
        SWITCH(55),
        SYNCHRONIZED(56),
        THIS(57),
        THROW(58),
        THROWS(59),
        TRANSIENT(60),
        TRUE(61),
        TRY(62),
        VOID(63),
        VOLATILE(64),
        WHILE(65),
        YIELD(66),
        REQUIRES(67),
        TO(68),
        WITH(69),
        OPEN(70),
        OPENS(71),
        USES(72),
        MODULE(73),
        EXPORTS(74),
        PROVIDES(75),
        TRANSITIVE(76),
        LONG_LITERAL(77),
        INTEGER_LITERAL(78),
        DECIMAL_LITERAL(79),
        HEX_LITERAL(80),
        OCTAL_LITERAL(81),
        BINARY_LITERAL(82),
        FLOATING_POINT_LITERAL(83),
        DECIMAL_FLOATING_POINT_LITERAL(84),
        DECIMAL_EXPONENT(85),
        HEXADECIMAL_FLOATING_POINT_LITERAL(86),
        HEXADECIMAL_EXPONENT(87),
        HEX_DIGITS(88),
        UNICODE_ESCAPE(89),
        CHARACTER_LITERAL(90),
        STRING_LITERAL(91),
        ENTER_TEXT_BLOCK(92),
        TEXT_BLOCK_LITERAL(93),
        TEXT_BLOCK_CONTENT(94),
        IDENTIFIER(95),
        LETTER(96),
        PART_LETTER(97),
        LPAREN(98),
        RPAREN(99),
        LBRACE(100),
        RBRACE(101),
        LBRACKET(102),
        RBRACKET(103),
        SEMICOLON(104),
        COMMA(105),
        DOT(106),
        AT(107),
        ASSIGN(108),
        LT(109),
        BANG(110),
        TILDE(111),
        HOOK(112),
        COLON(113),
        ARROW(114),
        EQ(115),
        GE(116),
        LE(117),
        NE(118),
        SC_AND(119),
        SC_OR(120),
        INCR(121),
        DECR(122),
        PLUS(123),
        MINUS(124),
        STAR(125),
        SLASH(126),
        BIT_AND(127),
        BIT_OR(128),
        XOR(129),
        REM(130),
        LSHIFT(131),
        PLUSASSIGN(132),
        MINUSASSIGN(133),
        STARASSIGN(134),
        SLASHASSIGN(135),
        ANDASSIGN(136),
        ORASSIGN(137),
        XORASSIGN(138),
        REMASSIGN(139),
        LSHIFTASSIGN(140),
        RSIGNEDSHIFTASSIGN(141),
        RUNSIGNEDSHIFTASSIGN(142),
        ELLIPSIS(143),
        DOUBLECOLON(144),
        RUNSIGNEDSHIFT(145),
        RSIGNEDSHIFT(146),
        GT(147),
        CTRL_Z(148);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 148:
                    return CTRL_Z;
                case 147:
                    return GT;
                case 146:
                    return RSIGNEDSHIFT;
                case 145:
                    return RUNSIGNEDSHIFT;
                case 144:
                    return DOUBLECOLON;
                case 143:
                    return ELLIPSIS;
                case 142:
                    return RUNSIGNEDSHIFTASSIGN;
                case 141:
                    return RSIGNEDSHIFTASSIGN;
                case 140:
                    return LSHIFTASSIGN;
                case 139:
                    return REMASSIGN;
                case 138:
                    return XORASSIGN;
                case 137:
                    return ORASSIGN;
                case 136:
                    return ANDASSIGN;
                case 135:
                    return SLASHASSIGN;
                case 134:
                    return STARASSIGN;
                case 133:
                    return MINUSASSIGN;
                case 132:
                    return PLUSASSIGN;
                case 131:
                    return LSHIFT;
                case 130:
                    return REM;
                case 129:
                    return XOR;
                case 128:
                    return BIT_OR;
                case 127:
                    return BIT_AND;
                case 126:
                    return SLASH;
                case 125:
                    return STAR;
                case 124:
                    return MINUS;
                case 123:
                    return PLUS;
                case 122:
                    return DECR;
                case 121:
                    return INCR;
                case 120:
                    return SC_OR;
                case 119:
                    return SC_AND;
                case 118:
                    return NE;
                case 117:
                    return LE;
                case 116:
                    return GE;
                case 115:
                    return EQ;
                case 114:
                    return ARROW;
                case 113:
                    return COLON;
                case 112:
                    return HOOK;
                case 111:
                    return TILDE;
                case 110:
                    return BANG;
                case 109:
                    return LT;
                case 108:
                    return ASSIGN;
                case 107:
                    return AT;
                case 106:
                    return DOT;
                case 105:
                    return COMMA;
                case 104:
                    return SEMICOLON;
                case 103:
                    return RBRACKET;
                case 102:
                    return LBRACKET;
                case 101:
                    return RBRACE;
                case 100:
                    return LBRACE;
                case 99:
                    return RPAREN;
                case 98:
                    return LPAREN;
                case 97:
                    return PART_LETTER;
                case 96:
                    return LETTER;
                case 95:
                    return IDENTIFIER;
                case 94:
                    return TEXT_BLOCK_CONTENT;
                case 93:
                    return TEXT_BLOCK_LITERAL;
                case 92:
                    return ENTER_TEXT_BLOCK;
                case 91:
                    return STRING_LITERAL;
                case 90:
                    return CHARACTER_LITERAL;
                case 89:
                    return UNICODE_ESCAPE;
                case 88:
                    return HEX_DIGITS;
                case 87:
                    return HEXADECIMAL_EXPONENT;
                case 86:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 85:
                    return DECIMAL_EXPONENT;
                case 84:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 83:
                    return FLOATING_POINT_LITERAL;
                case 82:
                    return BINARY_LITERAL;
                case 81:
                    return OCTAL_LITERAL;
                case 80:
                    return HEX_LITERAL;
                case 79:
                    return DECIMAL_LITERAL;
                case 78:
                    return INTEGER_LITERAL;
                case 77:
                    return LONG_LITERAL;
                case 76:
                    return TRANSITIVE;
                case 75:
                    return PROVIDES;
                case 74:
                    return EXPORTS;
                case 73:
                    return MODULE;
                case 72:
                    return USES;
                case 71:
                    return OPENS;
                case 70:
                    return OPEN;
                case 69:
                    return WITH;
                case 68:
                    return TO;
                case 67:
                    return REQUIRES;
                case 66:
                    return YIELD;
                case 65:
                    return WHILE;
                case 64:
                    return VOLATILE;
                case 63:
                    return VOID;
                case 62:
                    return TRY;
                case 61:
                    return TRUE;
                case 60:
                    return TRANSIENT;
                case 59:
                    return THROWS;
                case 58:
                    return THROW;
                case 57:
                    return THIS;
                case 56:
                    return SYNCHRONIZED;
                case 55:
                    return SWITCH;
                case 54:
                    return SUPER;
                case 53:
                    return STRICTFP;
                case 52:
                    return STATIC;
                case 51:
                    return SHORT;
                case 50:
                    return RETURN;
                case 49:
                    return PUBLIC;
                case 48:
                    return PROTECTED;
                case 47:
                    return PRIVATE;
                case 46:
                    return PACKAGE;
                case 45:
                    return NULL;
                case 44:
                    return NEW;
                case 43:
                    return NATIVE;
                case 42:
                    return LONG;
                case 41:
                    return INTERFACE;
                case 40:
                    return INT;
                case 39:
                    return INSTANCEOF;
                case 38:
                    return IMPORT;
                case 37:
                    return IMPLEMENTS;
                case 36:
                    return IF;
                case 35:
                    return GOTO;
                case 34:
                    return FOR;
                case 33:
                    return FLOAT;
                case 32:
                    return FINALLY;
                case 31:
                    return FINAL;
                case 30:
                    return FALSE;
                case 29:
                    return EXTENDS;
                case 28:
                    return ENUM;
                case 27:
                    return ELSE;
                case 26:
                    return DOUBLE;
                case 25:
                    return DO;
                case 24:
                    return _DEFAULT;
                case 23:
                    return CONTINUE;
                case 22:
                    return CONST;
                case 21:
                    return CLASS;
                case 20:
                    return CHAR;
                case 19:
                    return CATCH;
                case 18:
                    return CASE;
                case 17:
                    return BYTE;
                case 16:
                    return BREAK;
                case 15:
                    return BOOLEAN;
                case 14:
                    return ASSERT;
                case 13:
                    return ABSTRACT;
                case 12:
                    return COMMENT_CONTENT;
                case 11:
                    return MULTI_LINE_COMMENT;
                case 10:
                    return JAVADOC_COMMENT;
                case 9:
                    return ENTER_MULTILINE_COMMENT;
                case 8:
                    return ENTER_MULTILINE_JML;
                case 7:
                    return ENTER_JAVADOC_COMMENT;
                case 6:
                    return SINGLE_LINE_COMMENT;
                case 5:
                    return SINGLE_LINE_JML;
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
