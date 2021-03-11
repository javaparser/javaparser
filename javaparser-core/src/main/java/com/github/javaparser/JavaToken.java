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
        //You could be puzzled by the following lines
        //
        //The reason why these lines are necessary is the fact that Java is ambiguous. There are cases where the
        //sequence of characters ">>>" and ">>" should be recognized as the single tokens ">>>" and ">>". In other
        //cases however we want to split those characters in single GT tokens (">").
        //
        //For example, in expressions ">>" and ">>>" are valid, while when defining types we could have this:
        //
        //List<List<Set<String>>>>
        //
        //You can see that the sequence ">>>>" should be interpreted as four consecutive ">" tokens closing a type
        //parameter list.
        //
        //The JavaCC handle this case by first recognizing always the longest token, and then depending on the context
        //putting back the unused chars in the stream. However in those cases the token provided is invalid: it has an
        //image corresponding to the text originally recognized, without considering that after some characters could
        //have been put back into the stream.
        //
        //So in the case of:
        //
        //List<List<Set<String>>>>
        //___   -> recognized as ">>>", then ">>" put back in the stream but Token(type=GT, image=">>>") passed to this class
        //___  -> recognized as ">>>", then ">>" put back in the stream but Token(type=GT, image=">>>") passed to this class
        //__  -> recognized as ">>", then ">" put back in the stream but Token(type=GT, image=">>") passed to this class
        //_  -> Token(type=GT, image=">") good!
        //
        //So given the image could be wrong but the type is correct, we look at the type of the token and we fix
        //the image. Everybody is happy and we can keep this horrible thing as our little secret.
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
        JML_SINGLE_START0(5),
        SINGLE_LINE_COMMENT0(6),
        SINGLE_LINE_COMMENT(7),
        JML_SINGLE_START(8),
        JML_MULTI_START(9),
        JML_MULTI_END(10),
        JML_SINGLE_END(11),
        INVARIANT(12),
        INITIALLY(13),
        ENSURES(14),
        ASSIGNABLE(15),
        MODIFIABLE(16),
        MODIFIES(17),
        ACCESSIBLE(18),
        REPRESENTS(19),
        NESTED_CONTRACT_START(20),
        NESTED_CONTRACT_END(21),
        ALSO(22),
        PURE(23),
        STRICTLY_PURE(24),
        MODEL(25),
        HELPER(26),
        NULLABLE_BY_DEFAULT(27),
        NON_NULL(28),
        NULLABLE(29),
        BEHAVIOR(30),
        NORMAL_BEHAVIOR(31),
        EXCEPTIONAL_BEHAVIOR(32),
        MEASURED_BY(33),
        DETERMINES(34),
        BY(35),
        DECLASSIFIES(36),
        ERASES(37),
        NEW_OBJECT(38),
        SIGNALS(39),
        INSTANCE(40),
        ENTER_JAVADOC_COMMENT(41),
        ENTER_MULTILINE_COMMENT(42),
        JAVADOC_COMMENT(43),
        MULTI_LINE_COMMENT(44),
        COMMENT_CONTENT(45),
        ABSTRACT(46),
        ASSERT(47),
        BOOLEAN(48),
        BREAK(49),
        BYTE(50),
        CASE(51),
        CATCH(52),
        CHAR(53),
        CLASS(54),
        CONST(55),
        CONTINUE(56),
        _DEFAULT(57),
        DO(58),
        DOUBLE(59),
        ELSE(60),
        ENUM(61),
        EXTENDS(62),
        FALSE(63),
        FINAL(64),
        FINALLY(65),
        FLOAT(66),
        FOR(67),
        GOTO(68),
        IF(69),
        IMPLEMENTS(70),
        IMPORT(71),
        INSTANCEOF(72),
        INT(73),
        INTERFACE(74),
        LONG(75),
        NATIVE(76),
        NEW(77),
        NULL(78),
        PACKAGE(79),
        PRIVATE(80),
        PROTECTED(81),
        PUBLIC(82),
        RETURN(83),
        SHORT(84),
        STATIC(85),
        STRICTFP(86),
        SUPER(87),
        SWITCH(88),
        SYNCHRONIZED(89),
        THIS(90),
        THROW(91),
        THROWS(92),
        TRANSIENT(93),
        TRUE(94),
        TRY(95),
        VOID(96),
        VOLATILE(97),
        WHILE(98),
        YIELD(99),
        REQUIRES(100),
        TO(101),
        WITH(102),
        OPEN(103),
        OPENS(104),
        USES(105),
        MODULE(106),
        EXPORTS(107),
        PROVIDES(108),
        TRANSITIVE(109),
        LONG_LITERAL(110),
        INTEGER_LITERAL(111),
        DECIMAL_LITERAL(112),
        HEX_LITERAL(113),
        OCTAL_LITERAL(114),
        BINARY_LITERAL(115),
        FLOATING_POINT_LITERAL(116),
        DECIMAL_FLOATING_POINT_LITERAL(117),
        DECIMAL_EXPONENT(118),
        HEXADECIMAL_FLOATING_POINT_LITERAL(119),
        HEXADECIMAL_EXPONENT(120),
        HEX_DIGITS(121),
        UNICODE_ESCAPE(122),
        CHARACTER_LITERAL(123),
        STRING_LITERAL(124),
        ENTER_TEXT_BLOCK(125),
        TEXT_BLOCK_LITERAL(126),
        TEXT_BLOCK_CONTENT(127),
        IDENTIFIER(128),
        LETTER(129),
        PART_LETTER(130),
        LPAREN(131),
        RPAREN(132),
        LBRACE(133),
        RBRACE(134),
        LBRACKET(135),
        RBRACKET(136),
        SEMICOLON(137),
        COMMA(138),
        DOT(139),
        AT(140),
        ASSIGN(141),
        LT(142),
        BANG(143),
        TILDE(144),
        HOOK(145),
        COLON(146),
        ARROW(147),
        EQ(148),
        GE(149),
        LE(150),
        NE(151),
        SC_AND(152),
        SC_OR(153),
        INCR(154),
        DECR(155),
        PLUS(156),
        MINUS(157),
        STAR(158),
        SLASH(159),
        BIT_AND(160),
        BIT_OR(161),
        XOR(162),
        REM(163),
        LSHIFT(164),
        PLUSASSIGN(165),
        MINUSASSIGN(166),
        STARASSIGN(167),
        SLASHASSIGN(168),
        ANDASSIGN(169),
        ORASSIGN(170),
        XORASSIGN(171),
        REMASSIGN(172),
        LSHIFTASSIGN(173),
        RSIGNEDSHIFTASSIGN(174),
        RUNSIGNEDSHIFTASSIGN(175),
        ELLIPSIS(176),
        DOUBLECOLON(177),
        RUNSIGNEDSHIFT(178),
        RSIGNEDSHIFT(179),
        GT(180),
        CTRL_Z(181);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 181:
                    return CTRL_Z;
                case 180:
                    return GT;
                case 179:
                    return RSIGNEDSHIFT;
                case 178:
                    return RUNSIGNEDSHIFT;
                case 177:
                    return DOUBLECOLON;
                case 176:
                    return ELLIPSIS;
                case 175:
                    return RUNSIGNEDSHIFTASSIGN;
                case 174:
                    return RSIGNEDSHIFTASSIGN;
                case 173:
                    return LSHIFTASSIGN;
                case 172:
                    return REMASSIGN;
                case 171:
                    return XORASSIGN;
                case 170:
                    return ORASSIGN;
                case 169:
                    return ANDASSIGN;
                case 168:
                    return SLASHASSIGN;
                case 167:
                    return STARASSIGN;
                case 166:
                    return MINUSASSIGN;
                case 165:
                    return PLUSASSIGN;
                case 164:
                    return LSHIFT;
                case 163:
                    return REM;
                case 162:
                    return XOR;
                case 161:
                    return BIT_OR;
                case 160:
                    return BIT_AND;
                case 159:
                    return SLASH;
                case 158:
                    return STAR;
                case 157:
                    return MINUS;
                case 156:
                    return PLUS;
                case 155:
                    return DECR;
                case 154:
                    return INCR;
                case 153:
                    return SC_OR;
                case 152:
                    return SC_AND;
                case 151:
                    return NE;
                case 150:
                    return LE;
                case 149:
                    return GE;
                case 148:
                    return EQ;
                case 147:
                    return ARROW;
                case 146:
                    return COLON;
                case 145:
                    return HOOK;
                case 144:
                    return TILDE;
                case 143:
                    return BANG;
                case 142:
                    return LT;
                case 141:
                    return ASSIGN;
                case 140:
                    return AT;
                case 139:
                    return DOT;
                case 138:
                    return COMMA;
                case 137:
                    return SEMICOLON;
                case 136:
                    return RBRACKET;
                case 135:
                    return LBRACKET;
                case 134:
                    return RBRACE;
                case 133:
                    return LBRACE;
                case 132:
                    return RPAREN;
                case 131:
                    return LPAREN;
                case 130:
                    return PART_LETTER;
                case 129:
                    return LETTER;
                case 128:
                    return IDENTIFIER;
                case 127:
                    return TEXT_BLOCK_CONTENT;
                case 126:
                    return TEXT_BLOCK_LITERAL;
                case 125:
                    return ENTER_TEXT_BLOCK;
                case 124:
                    return STRING_LITERAL;
                case 123:
                    return CHARACTER_LITERAL;
                case 122:
                    return UNICODE_ESCAPE;
                case 121:
                    return HEX_DIGITS;
                case 120:
                    return HEXADECIMAL_EXPONENT;
                case 119:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 118:
                    return DECIMAL_EXPONENT;
                case 117:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 116:
                    return FLOATING_POINT_LITERAL;
                case 115:
                    return BINARY_LITERAL;
                case 114:
                    return OCTAL_LITERAL;
                case 113:
                    return HEX_LITERAL;
                case 112:
                    return DECIMAL_LITERAL;
                case 111:
                    return INTEGER_LITERAL;
                case 110:
                    return LONG_LITERAL;
                case 109:
                    return TRANSITIVE;
                case 108:
                    return PROVIDES;
                case 107:
                    return EXPORTS;
                case 106:
                    return MODULE;
                case 105:
                    return USES;
                case 104:
                    return OPENS;
                case 103:
                    return OPEN;
                case 102:
                    return WITH;
                case 101:
                    return TO;
                case 100:
                    return REQUIRES;
                case 99:
                    return YIELD;
                case 98:
                    return WHILE;
                case 97:
                    return VOLATILE;
                case 96:
                    return VOID;
                case 95:
                    return TRY;
                case 94:
                    return TRUE;
                case 93:
                    return TRANSIENT;
                case 92:
                    return THROWS;
                case 91:
                    return THROW;
                case 90:
                    return THIS;
                case 89:
                    return SYNCHRONIZED;
                case 88:
                    return SWITCH;
                case 87:
                    return SUPER;
                case 86:
                    return STRICTFP;
                case 85:
                    return STATIC;
                case 84:
                    return SHORT;
                case 83:
                    return RETURN;
                case 82:
                    return PUBLIC;
                case 81:
                    return PROTECTED;
                case 80:
                    return PRIVATE;
                case 79:
                    return PACKAGE;
                case 78:
                    return NULL;
                case 77:
                    return NEW;
                case 76:
                    return NATIVE;
                case 75:
                    return LONG;
                case 74:
                    return INTERFACE;
                case 73:
                    return INT;
                case 72:
                    return INSTANCEOF;
                case 71:
                    return IMPORT;
                case 70:
                    return IMPLEMENTS;
                case 69:
                    return IF;
                case 68:
                    return GOTO;
                case 67:
                    return FOR;
                case 66:
                    return FLOAT;
                case 65:
                    return FINALLY;
                case 64:
                    return FINAL;
                case 63:
                    return FALSE;
                case 62:
                    return EXTENDS;
                case 61:
                    return ENUM;
                case 60:
                    return ELSE;
                case 59:
                    return DOUBLE;
                case 58:
                    return DO;
                case 57:
                    return _DEFAULT;
                case 56:
                    return CONTINUE;
                case 55:
                    return CONST;
                case 54:
                    return CLASS;
                case 53:
                    return CHAR;
                case 52:
                    return CATCH;
                case 51:
                    return CASE;
                case 50:
                    return BYTE;
                case 49:
                    return BREAK;
                case 48:
                    return BOOLEAN;
                case 47:
                    return ASSERT;
                case 46:
                    return ABSTRACT;
                case 45:
                    return COMMENT_CONTENT;
                case 44:
                    return MULTI_LINE_COMMENT;
                case 43:
                    return JAVADOC_COMMENT;
                case 42:
                    return ENTER_MULTILINE_COMMENT;
                case 41:
                    return ENTER_JAVADOC_COMMENT;
                case 40:
                    return INSTANCE;
                case 39:
                    return SIGNALS;
                case 38:
                    return NEW_OBJECT;
                case 37:
                    return ERASES;
                case 36:
                    return DECLASSIFIES;
                case 35:
                    return BY;
                case 34:
                    return DETERMINES;
                case 33:
                    return MEASURED_BY;
                case 32:
                    return EXCEPTIONAL_BEHAVIOR;
                case 31:
                    return NORMAL_BEHAVIOR;
                case 30:
                    return BEHAVIOR;
                case 29:
                    return NULLABLE;
                case 28:
                    return NON_NULL;
                case 27:
                    return NULLABLE_BY_DEFAULT;
                case 26:
                    return HELPER;
                case 25:
                    return MODEL;
                case 24:
                    return STRICTLY_PURE;
                case 23:
                    return PURE;
                case 22:
                    return ALSO;
                case 21:
                    return NESTED_CONTRACT_END;
                case 20:
                    return NESTED_CONTRACT_START;
                case 19:
                    return REPRESENTS;
                case 18:
                    return ACCESSIBLE;
                case 17:
                    return MODIFIES;
                case 16:
                    return MODIFIABLE;
                case 15:
                    return ASSIGNABLE;
                case 14:
                    return ENSURES;
                case 13:
                    return INITIALLY;
                case 12:
                    return INVARIANT;
                case 11:
                    return JML_SINGLE_END;
                case 10:
                    return JML_MULTI_END;
                case 9:
                    return JML_MULTI_START;
                case 8:
                    return JML_SINGLE_START;
                case 7:
                    return SINGLE_LINE_COMMENT;
                case 6:
                    return SINGLE_LINE_COMMENT0;
                case 5:
                    return JML_SINGLE_START0;
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
        return text.equals(javaToken.text);
    }
}
