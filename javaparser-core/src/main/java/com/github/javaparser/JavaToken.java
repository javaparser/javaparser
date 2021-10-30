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
        RECORD(48),
        RETURN(49),
        SHORT(50),
        STATIC(51),
        STRICTFP(52),
        SUPER(53),
        SWITCH(54),
        SYNCHRONIZED(55),
        THIS(56),
        THROW(57),
        THROWS(58),
        TRANSIENT(59),
        TRUE(60),
        TRY(61),
        VOID(62),
        VOLATILE(63),
        WHILE(64),
        YIELD(65),
        REQUIRES(66),
        TO(67),
        WITH(68),
        OPEN(69),
        OPENS(70),
        USES(71),
        MODULE(72),
        EXPORTS(73),
        PROVIDES(74),
        TRANSITIVE(75),
        TRANSACTIONBEGIN(76),
        TRANSACTIONCOMMIT(77),
        TRANSACTIONFINISH(78),
        TRANSACTIONABORT(79),
        RETURNTYPE(80),
        SEQ(81),
        SET(82),
        LOOPSCOPE(83),
        MAP(84),
        MERGE_POINT(85),
        METHODFRAME(86),
        LOCSET(87),
        FREE(88),
        EXEC(89),
        CONTINUETYPE(90),
        CCATCH(91),
        BREAKTYPE(92),
        BIGINT(93),
        REAL(94),
        MAP_FUNCTION(95),
        LONG_LITERAL(96),
        INTEGER_LITERAL(97),
        DECIMAL_LITERAL(98),
        HEX_LITERAL(99),
        OCTAL_LITERAL(100),
        BINARY_LITERAL(101),
        FLOATING_POINT_LITERAL(102),
        DECIMAL_FLOATING_POINT_LITERAL(103),
        DECIMAL_EXPONENT(104),
        HEXADECIMAL_FLOATING_POINT_LITERAL(105),
        HEXADECIMAL_EXPONENT(106),
        HEX_DIGITS(107),
        UNICODE_ESCAPE(108),
        CHARACTER_LITERAL(109),
        STRING_LITERAL(110),
        ENTER_TEXT_BLOCK(111),
        TEXT_BLOCK_LITERAL(112),
        TEXT_BLOCK_CONTENT(113),
        IDENTIFIER(114),
        JMLIDENTIFIER(115),
        LETTER(116),
        PART_LETTER(117),
        LPAREN(118),
        RPAREN(119),
        LBRACE(120),
        RBRACE(121),
        LBRACKET(122),
        RBRACKET(123),
        SEMICOLON(124),
        COMMA(125),
        DOT(126),
        ELLIPSIS(127),
        AT(128),
        DOUBLECOLON(129),
        ASSIGN(130),
        LT(131),
        BANG(132),
        TILDE(133),
        HOOK(134),
        COLON(135),
        ARROW(136),
        EQ(137),
        GE(138),
        LE(139),
        NE(140),
        SC_AND(141),
        SC_OR(142),
        INCR(143),
        DECR(144),
        PLUS(145),
        MINUS(146),
        STAR(147),
        SLASH(148),
        BIT_AND(149),
        BIT_OR(150),
        XOR(151),
        REM(152),
        LSHIFT(153),
        PLUSASSIGN(154),
        MINUSASSIGN(155),
        STARASSIGN(156),
        SLASHASSIGN(157),
        ANDASSIGN(158),
        ORASSIGN(159),
        XORASSIGN(160),
        REMASSIGN(161),
        LSHIFTASSIGN(162),
        RSIGNEDSHIFTASSIGN(163),
        RUNSIGNEDSHIFTASSIGN(164),
        RUNSIGNEDSHIFT(165),
        RSIGNEDSHIFT(166),
        GT(167),
        CTRL_Z(168);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 168:
                    return CTRL_Z;
                case 167:
                    return GT;
                case 166:
                    return RSIGNEDSHIFT;
                case 165:
                    return RUNSIGNEDSHIFT;
                case 164:
                    return RUNSIGNEDSHIFTASSIGN;
                case 163:
                    return RSIGNEDSHIFTASSIGN;
                case 162:
                    return LSHIFTASSIGN;
                case 161:
                    return REMASSIGN;
                case 160:
                    return XORASSIGN;
                case 159:
                    return ORASSIGN;
                case 158:
                    return ANDASSIGN;
                case 157:
                    return SLASHASSIGN;
                case 156:
                    return STARASSIGN;
                case 155:
                    return MINUSASSIGN;
                case 154:
                    return PLUSASSIGN;
                case 153:
                    return LSHIFT;
                case 152:
                    return REM;
                case 151:
                    return XOR;
                case 150:
                    return BIT_OR;
                case 149:
                    return BIT_AND;
                case 148:
                    return SLASH;
                case 147:
                    return STAR;
                case 146:
                    return MINUS;
                case 145:
                    return PLUS;
                case 144:
                    return DECR;
                case 143:
                    return INCR;
                case 142:
                    return SC_OR;
                case 141:
                    return SC_AND;
                case 140:
                    return NE;
                case 139:
                    return LE;
                case 138:
                    return GE;
                case 137:
                    return EQ;
                case 136:
                    return ARROW;
                case 135:
                    return COLON;
                case 134:
                    return HOOK;
                case 133:
                    return TILDE;
                case 132:
                    return BANG;
                case 131:
                    return LT;
                case 130:
                    return ASSIGN;
                case 129:
                    return DOUBLECOLON;
                case 128:
                    return AT;
                case 127:
                    return ELLIPSIS;
                case 126:
                    return DOT;
                case 125:
                    return COMMA;
                case 124:
                    return SEMICOLON;
                case 123:
                    return RBRACKET;
                case 122:
                    return LBRACKET;
                case 121:
                    return RBRACE;
                case 120:
                    return LBRACE;
                case 119:
                    return RPAREN;
                case 118:
                    return LPAREN;
                case 117:
                    return PART_LETTER;
                case 116:
                    return LETTER;
                case 115:
                    return JMLIDENTIFIER;
                case 114:
                    return IDENTIFIER;
                case 113:
                    return TEXT_BLOCK_CONTENT;
                case 112:
                    return TEXT_BLOCK_LITERAL;
                case 111:
                    return ENTER_TEXT_BLOCK;
                case 110:
                    return STRING_LITERAL;
                case 109:
                    return CHARACTER_LITERAL;
                case 108:
                    return UNICODE_ESCAPE;
                case 107:
                    return HEX_DIGITS;
                case 106:
                    return HEXADECIMAL_EXPONENT;
                case 105:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 104:
                    return DECIMAL_EXPONENT;
                case 103:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 102:
                    return FLOATING_POINT_LITERAL;
                case 101:
                    return BINARY_LITERAL;
                case 100:
                    return OCTAL_LITERAL;
                case 99:
                    return HEX_LITERAL;
                case 98:
                    return DECIMAL_LITERAL;
                case 97:
                    return INTEGER_LITERAL;
                case 96:
                    return LONG_LITERAL;
                case 95:
                    return MAP_FUNCTION;
                case 94:
                    return REAL;
                case 93:
                    return BIGINT;
                case 92:
                    return BREAKTYPE;
                case 91:
                    return CCATCH;
                case 90:
                    return CONTINUETYPE;
                case 89:
                    return EXEC;
                case 88:
                    return FREE;
                case 87:
                    return LOCSET;
                case 86:
                    return METHODFRAME;
                case 85:
                    return MERGE_POINT;
                case 84:
                    return MAP;
                case 83:
                    return LOOPSCOPE;
                case 82:
                    return SET;
                case 81:
                    return SEQ;
                case 80:
                    return RETURNTYPE;
                case 79:
                    return TRANSACTIONABORT;
                case 78:
                    return TRANSACTIONFINISH;
                case 77:
                    return TRANSACTIONCOMMIT;
                case 76:
                    return TRANSACTIONBEGIN;
                case 75:
                    return TRANSITIVE;
                case 74:
                    return PROVIDES;
                case 73:
                    return EXPORTS;
                case 72:
                    return MODULE;
                case 71:
                    return USES;
                case 70:
                    return OPENS;
                case 69:
                    return OPEN;
                case 68:
                    return WITH;
                case 67:
                    return TO;
                case 66:
                    return REQUIRES;
                case 65:
                    return YIELD;
                case 64:
                    return WHILE;
                case 63:
                    return VOLATILE;
                case 62:
                    return VOID;
                case 61:
                    return TRY;
                case 60:
                    return TRUE;
                case 59:
                    return TRANSIENT;
                case 58:
                    return THROWS;
                case 57:
                    return THROW;
                case 56:
                    return THIS;
                case 55:
                    return SYNCHRONIZED;
                case 54:
                    return SWITCH;
                case 53:
                    return SUPER;
                case 52:
                    return STRICTFP;
                case 51:
                    return STATIC;
                case 50:
                    return SHORT;
                case 49:
                    return RETURN;
                case 48:
                    return RECORD;
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
