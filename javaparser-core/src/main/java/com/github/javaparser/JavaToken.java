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
        SUCH_THAT(15),
        DIVERGES(16),
        SIGNALS_ONLY(17),
        RETURNS(18),
        BREAKS(19),
        CONTINUES(20),
        BREAK_BEHAVIOR(21),
        CONTINUE_BEHAVIOR(22),
        RETURN_BEHAVIOR(23),
        ASSIGNABLE(24),
        MODIFIABLE(25),
        MODIFIES(26),
        ACCESSIBLE(27),
        REPRESENTS(28),
        NESTED_CONTRACT_START(29),
        NESTED_CONTRACT_END(30),
        ALSO(31),
        PURE(32),
        STRICTLY_PURE(33),
        MODEL(34),
        HELPER(35),
        NULLABLE_BY_DEFAULT(36),
        NON_NULL(37),
        NULLABLE(38),
        BEHAVIOR(39),
        NORMAL_BEHAVIOR(40),
        EXCEPTIONAL_BEHAVIOR(41),
        MEASURED_BY(42),
        DETERMINES(43),
        BY(44),
        DECLASSIFIES(45),
        ERASES(46),
        NEW_OBJECT(47),
        SIGNALS(48),
        INSTANCE(49),
        ENTER_JAVADOC_COMMENT(50),
        ENTER_MULTILINE_COMMENT(51),
        JAVADOC_COMMENT(52),
        MULTI_LINE_COMMENT(53),
        COMMENT_CONTENT(54),
        ABSTRACT(55),
        ASSERT(56),
        BOOLEAN(57),
        BREAK(58),
        BYTE(59),
        CASE(60),
        CATCH(61),
        CHAR(62),
        CLASS(63),
        CONST(64),
        CONTINUE(65),
        _DEFAULT(66),
        DO(67),
        DOUBLE(68),
        ELSE(69),
        ENUM(70),
        EXTENDS(71),
        FALSE(72),
        FINAL(73),
        FINALLY(74),
        FLOAT(75),
        FOR(76),
        GOTO(77),
        IF(78),
        IMPLEMENTS(79),
        IMPORT(80),
        INSTANCEOF(81),
        INT(82),
        INTERFACE(83),
        LONG(84),
        NATIVE(85),
        NEW(86),
        NULL(87),
        PACKAGE(88),
        PRIVATE(89),
        PROTECTED(90),
        PUBLIC(91),
        RETURN(92),
        SHORT(93),
        STATIC(94),
        STRICTFP(95),
        SUPER(96),
        SWITCH(97),
        SYNCHRONIZED(98),
        THIS(99),
        THROW(100),
        THROWS(101),
        TRANSIENT(102),
        TRUE(103),
        TRY(104),
        VOID(105),
        VOLATILE(106),
        WHILE(107),
        YIELD(108),
        REQUIRES(109),
        TO(110),
        WITH(111),
        OPEN(112),
        OPENS(113),
        USES(114),
        MODULE(115),
        EXPORTS(116),
        PROVIDES(117),
        TRANSITIVE(118),
        LONG_LITERAL(119),
        INTEGER_LITERAL(120),
        DECIMAL_LITERAL(121),
        HEX_LITERAL(122),
        OCTAL_LITERAL(123),
        BINARY_LITERAL(124),
        FLOATING_POINT_LITERAL(125),
        DECIMAL_FLOATING_POINT_LITERAL(126),
        DECIMAL_EXPONENT(127),
        HEXADECIMAL_FLOATING_POINT_LITERAL(128),
        HEXADECIMAL_EXPONENT(129),
        HEX_DIGITS(130),
        UNICODE_ESCAPE(131),
        CHARACTER_LITERAL(132),
        STRING_LITERAL(133),
        ENTER_TEXT_BLOCK(134),
        TEXT_BLOCK_LITERAL(135),
        TEXT_BLOCK_CONTENT(136),
        IDENTIFIER(137),
        LETTER(138),
        PART_LETTER(139),
        LPAREN(140),
        RPAREN(141),
        LBRACE(142),
        RBRACE(143),
        LBRACKET(144),
        RBRACKET(145),
        SEMICOLON(146),
        COMMA(147),
        DOT(148),
        AT(149),
        ASSIGN(150),
        LT(151),
        BANG(152),
        TILDE(153),
        HOOK(154),
        COLON(155),
        ARROW(156),
        EQ(157),
        GE(158),
        LE(159),
        NE(160),
        SC_AND(161),
        SC_OR(162),
        INCR(163),
        DECR(164),
        PLUS(165),
        MINUS(166),
        STAR(167),
        SLASH(168),
        BIT_AND(169),
        BIT_OR(170),
        XOR(171),
        REM(172),
        LSHIFT(173),
        PLUSASSIGN(174),
        MINUSASSIGN(175),
        STARASSIGN(176),
        SLASHASSIGN(177),
        ANDASSIGN(178),
        ORASSIGN(179),
        XORASSIGN(180),
        REMASSIGN(181),
        LSHIFTASSIGN(182),
        RSIGNEDSHIFTASSIGN(183),
        RUNSIGNEDSHIFTASSIGN(184),
        ELLIPSIS(185),
        DOUBLECOLON(186),
        RUNSIGNEDSHIFT(187),
        RSIGNEDSHIFT(188),
        GT(189),
        CTRL_Z(190);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 190:
                    return CTRL_Z;
                case 189:
                    return GT;
                case 188:
                    return RSIGNEDSHIFT;
                case 187:
                    return RUNSIGNEDSHIFT;
                case 186:
                    return DOUBLECOLON;
                case 185:
                    return ELLIPSIS;
                case 184:
                    return RUNSIGNEDSHIFTASSIGN;
                case 183:
                    return RSIGNEDSHIFTASSIGN;
                case 182:
                    return LSHIFTASSIGN;
                case 181:
                    return REMASSIGN;
                case 180:
                    return XORASSIGN;
                case 179:
                    return ORASSIGN;
                case 178:
                    return ANDASSIGN;
                case 177:
                    return SLASHASSIGN;
                case 176:
                    return STARASSIGN;
                case 175:
                    return MINUSASSIGN;
                case 174:
                    return PLUSASSIGN;
                case 173:
                    return LSHIFT;
                case 172:
                    return REM;
                case 171:
                    return XOR;
                case 170:
                    return BIT_OR;
                case 169:
                    return BIT_AND;
                case 168:
                    return SLASH;
                case 167:
                    return STAR;
                case 166:
                    return MINUS;
                case 165:
                    return PLUS;
                case 164:
                    return DECR;
                case 163:
                    return INCR;
                case 162:
                    return SC_OR;
                case 161:
                    return SC_AND;
                case 160:
                    return NE;
                case 159:
                    return LE;
                case 158:
                    return GE;
                case 157:
                    return EQ;
                case 156:
                    return ARROW;
                case 155:
                    return COLON;
                case 154:
                    return HOOK;
                case 153:
                    return TILDE;
                case 152:
                    return BANG;
                case 151:
                    return LT;
                case 150:
                    return ASSIGN;
                case 149:
                    return AT;
                case 148:
                    return DOT;
                case 147:
                    return COMMA;
                case 146:
                    return SEMICOLON;
                case 145:
                    return RBRACKET;
                case 144:
                    return LBRACKET;
                case 143:
                    return RBRACE;
                case 142:
                    return LBRACE;
                case 141:
                    return RPAREN;
                case 140:
                    return LPAREN;
                case 139:
                    return PART_LETTER;
                case 138:
                    return LETTER;
                case 137:
                    return IDENTIFIER;
                case 136:
                    return TEXT_BLOCK_CONTENT;
                case 135:
                    return TEXT_BLOCK_LITERAL;
                case 134:
                    return ENTER_TEXT_BLOCK;
                case 133:
                    return STRING_LITERAL;
                case 132:
                    return CHARACTER_LITERAL;
                case 131:
                    return UNICODE_ESCAPE;
                case 130:
                    return HEX_DIGITS;
                case 129:
                    return HEXADECIMAL_EXPONENT;
                case 128:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 127:
                    return DECIMAL_EXPONENT;
                case 126:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 125:
                    return FLOATING_POINT_LITERAL;
                case 124:
                    return BINARY_LITERAL;
                case 123:
                    return OCTAL_LITERAL;
                case 122:
                    return HEX_LITERAL;
                case 121:
                    return DECIMAL_LITERAL;
                case 120:
                    return INTEGER_LITERAL;
                case 119:
                    return LONG_LITERAL;
                case 118:
                    return TRANSITIVE;
                case 117:
                    return PROVIDES;
                case 116:
                    return EXPORTS;
                case 115:
                    return MODULE;
                case 114:
                    return USES;
                case 113:
                    return OPENS;
                case 112:
                    return OPEN;
                case 111:
                    return WITH;
                case 110:
                    return TO;
                case 109:
                    return REQUIRES;
                case 108:
                    return YIELD;
                case 107:
                    return WHILE;
                case 106:
                    return VOLATILE;
                case 105:
                    return VOID;
                case 104:
                    return TRY;
                case 103:
                    return TRUE;
                case 102:
                    return TRANSIENT;
                case 101:
                    return THROWS;
                case 100:
                    return THROW;
                case 99:
                    return THIS;
                case 98:
                    return SYNCHRONIZED;
                case 97:
                    return SWITCH;
                case 96:
                    return SUPER;
                case 95:
                    return STRICTFP;
                case 94:
                    return STATIC;
                case 93:
                    return SHORT;
                case 92:
                    return RETURN;
                case 91:
                    return PUBLIC;
                case 90:
                    return PROTECTED;
                case 89:
                    return PRIVATE;
                case 88:
                    return PACKAGE;
                case 87:
                    return NULL;
                case 86:
                    return NEW;
                case 85:
                    return NATIVE;
                case 84:
                    return LONG;
                case 83:
                    return INTERFACE;
                case 82:
                    return INT;
                case 81:
                    return INSTANCEOF;
                case 80:
                    return IMPORT;
                case 79:
                    return IMPLEMENTS;
                case 78:
                    return IF;
                case 77:
                    return GOTO;
                case 76:
                    return FOR;
                case 75:
                    return FLOAT;
                case 74:
                    return FINALLY;
                case 73:
                    return FINAL;
                case 72:
                    return FALSE;
                case 71:
                    return EXTENDS;
                case 70:
                    return ENUM;
                case 69:
                    return ELSE;
                case 68:
                    return DOUBLE;
                case 67:
                    return DO;
                case 66:
                    return _DEFAULT;
                case 65:
                    return CONTINUE;
                case 64:
                    return CONST;
                case 63:
                    return CLASS;
                case 62:
                    return CHAR;
                case 61:
                    return CATCH;
                case 60:
                    return CASE;
                case 59:
                    return BYTE;
                case 58:
                    return BREAK;
                case 57:
                    return BOOLEAN;
                case 56:
                    return ASSERT;
                case 55:
                    return ABSTRACT;
                case 54:
                    return COMMENT_CONTENT;
                case 53:
                    return MULTI_LINE_COMMENT;
                case 52:
                    return JAVADOC_COMMENT;
                case 51:
                    return ENTER_MULTILINE_COMMENT;
                case 50:
                    return ENTER_JAVADOC_COMMENT;
                case 49:
                    return INSTANCE;
                case 48:
                    return SIGNALS;
                case 47:
                    return NEW_OBJECT;
                case 46:
                    return ERASES;
                case 45:
                    return DECLASSIFIES;
                case 44:
                    return BY;
                case 43:
                    return DETERMINES;
                case 42:
                    return MEASURED_BY;
                case 41:
                    return EXCEPTIONAL_BEHAVIOR;
                case 40:
                    return NORMAL_BEHAVIOR;
                case 39:
                    return BEHAVIOR;
                case 38:
                    return NULLABLE;
                case 37:
                    return NON_NULL;
                case 36:
                    return NULLABLE_BY_DEFAULT;
                case 35:
                    return HELPER;
                case 34:
                    return MODEL;
                case 33:
                    return STRICTLY_PURE;
                case 32:
                    return PURE;
                case 31:
                    return ALSO;
                case 30:
                    return NESTED_CONTRACT_END;
                case 29:
                    return NESTED_CONTRACT_START;
                case 28:
                    return REPRESENTS;
                case 27:
                    return ACCESSIBLE;
                case 26:
                    return MODIFIES;
                case 25:
                    return MODIFIABLE;
                case 24:
                    return ASSIGNABLE;
                case 23:
                    return RETURN_BEHAVIOR;
                case 22:
                    return CONTINUE_BEHAVIOR;
                case 21:
                    return BREAK_BEHAVIOR;
                case 20:
                    return CONTINUES;
                case 19:
                    return BREAKS;
                case 18:
                    return RETURNS;
                case 17:
                    return SIGNALS_ONLY;
                case 16:
                    return DIVERGES;
                case 15:
                    return SUCH_THAT;
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
