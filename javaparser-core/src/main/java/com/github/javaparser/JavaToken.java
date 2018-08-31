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
        REQUIRES(64),
        TO(65),
        WITH(66),
        OPEN(67),
        OPENS(68),
        USES(69),
        MODULE(70),
        EXPORTS(71),
        PROVIDES(72),
        TRANSITIVE(73),
        LONG_LITERAL(74),
        INTEGER_LITERAL(75),
        DECIMAL_LITERAL(76),
        HEX_LITERAL(77),
        OCTAL_LITERAL(78),
        BINARY_LITERAL(79),
        FLOATING_POINT_LITERAL(80),
        DECIMAL_FLOATING_POINT_LITERAL(81),
        DECIMAL_EXPONENT(82),
        HEXADECIMAL_FLOATING_POINT_LITERAL(83),
        HEXADECIMAL_EXPONENT(84),
        HEX_DIGITS(85),
        UNICODE_ESCAPE(86),
        CHARACTER_LITERAL(87),
        STRING_LITERAL(88),
        IDENTIFIER(89),
        LETTER(90),
        PART_LETTER(91),
        LPAREN(92),
        RPAREN(93),
        LBRACE(94),
        RBRACE(95),
        LBRACKET(96),
        RBRACKET(97),
        SEMICOLON(98),
        COMMA(99),
        DOT(100),
        AT(101),
        ASSIGN(102),
        LT(103),
        BANG(104),
        TILDE(105),
        HOOK(106),
        COLON(107),
        EQ(108),
        LE(109),
        GE(110),
        NE(111),
        SC_OR(112),
        SC_AND(113),
        INCR(114),
        DECR(115),
        PLUS(116),
        MINUS(117),
        STAR(118),
        SLASH(119),
        BIT_AND(120),
        BIT_OR(121),
        XOR(122),
        REM(123),
        LSHIFT(124),
        PLUSASSIGN(125),
        MINUSASSIGN(126),
        STARASSIGN(127),
        SLASHASSIGN(128),
        ANDASSIGN(129),
        ORASSIGN(130),
        XORASSIGN(131),
        REMASSIGN(132),
        LSHIFTASSIGN(133),
        RSIGNEDSHIFTASSIGN(134),
        RUNSIGNEDSHIFTASSIGN(135),
        ELLIPSIS(136),
        ARROW(137),
        DOUBLECOLON(138),
        RUNSIGNEDSHIFT(139),
        RSIGNEDSHIFT(140),
        GT(141),
        CTRL_Z(142);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 142:
                    return CTRL_Z;
                case 141:
                    return GT;
                case 140:
                    return RSIGNEDSHIFT;
                case 139:
                    return RUNSIGNEDSHIFT;
                case 138:
                    return DOUBLECOLON;
                case 137:
                    return ARROW;
                case 136:
                    return ELLIPSIS;
                case 135:
                    return RUNSIGNEDSHIFTASSIGN;
                case 134:
                    return RSIGNEDSHIFTASSIGN;
                case 133:
                    return LSHIFTASSIGN;
                case 132:
                    return REMASSIGN;
                case 131:
                    return XORASSIGN;
                case 130:
                    return ORASSIGN;
                case 129:
                    return ANDASSIGN;
                case 128:
                    return SLASHASSIGN;
                case 127:
                    return STARASSIGN;
                case 126:
                    return MINUSASSIGN;
                case 125:
                    return PLUSASSIGN;
                case 124:
                    return LSHIFT;
                case 123:
                    return REM;
                case 122:
                    return XOR;
                case 121:
                    return BIT_OR;
                case 120:
                    return BIT_AND;
                case 119:
                    return SLASH;
                case 118:
                    return STAR;
                case 117:
                    return MINUS;
                case 116:
                    return PLUS;
                case 115:
                    return DECR;
                case 114:
                    return INCR;
                case 113:
                    return SC_AND;
                case 112:
                    return SC_OR;
                case 111:
                    return NE;
                case 110:
                    return GE;
                case 109:
                    return LE;
                case 108:
                    return EQ;
                case 107:
                    return COLON;
                case 106:
                    return HOOK;
                case 105:
                    return TILDE;
                case 104:
                    return BANG;
                case 103:
                    return LT;
                case 102:
                    return ASSIGN;
                case 101:
                    return AT;
                case 100:
                    return DOT;
                case 99:
                    return COMMA;
                case 98:
                    return SEMICOLON;
                case 97:
                    return RBRACKET;
                case 96:
                    return LBRACKET;
                case 95:
                    return RBRACE;
                case 94:
                    return LBRACE;
                case 93:
                    return RPAREN;
                case 92:
                    return LPAREN;
                case 91:
                    return PART_LETTER;
                case 90:
                    return LETTER;
                case 89:
                    return IDENTIFIER;
                case 88:
                    return STRING_LITERAL;
                case 87:
                    return CHARACTER_LITERAL;
                case 86:
                    return UNICODE_ESCAPE;
                case 85:
                    return HEX_DIGITS;
                case 84:
                    return HEXADECIMAL_EXPONENT;
                case 83:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 82:
                    return DECIMAL_EXPONENT;
                case 81:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 80:
                    return FLOATING_POINT_LITERAL;
                case 79:
                    return BINARY_LITERAL;
                case 78:
                    return OCTAL_LITERAL;
                case 77:
                    return HEX_LITERAL;
                case 76:
                    return DECIMAL_LITERAL;
                case 75:
                    return INTEGER_LITERAL;
                case 74:
                    return LONG_LITERAL;
                case 73:
                    return TRANSITIVE;
                case 72:
                    return PROVIDES;
                case 71:
                    return EXPORTS;
                case 70:
                    return MODULE;
                case 69:
                    return USES;
                case 68:
                    return OPENS;
                case 67:
                    return OPEN;
                case 66:
                    return WITH;
                case 65:
                    return TO;
                case 64:
                    return REQUIRES;
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
