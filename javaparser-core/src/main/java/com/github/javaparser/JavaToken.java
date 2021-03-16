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
        GHOST(39),
        SPEC_PUBLIC(40),
        SPEC_PRIVATE(41),
        SPEC_PACKAGE(42),
        SPEC_PROTECTED(43),
        BEHAVIOR(44),
        NORMAL_BEHAVIOR(45),
        EXCEPTIONAL_BEHAVIOR(46),
        MEASURED_BY(47),
        DETERMINES(48),
        BY(49),
        DECLASSIFIES(50),
        ERASES(51),
        NEW_OBJECT(52),
        SIGNALS(53),
        INSTANCE(54),
        ENTER_JAVADOC_COMMENT(55),
        ENTER_MULTILINE_COMMENT(56),
        JAVADOC_COMMENT(57),
        MULTI_LINE_COMMENT(58),
        COMMENT_CONTENT(59),
        ABSTRACT(60),
        ASSERT(61),
        BOOLEAN(62),
        BREAK(63),
        BYTE(64),
        CASE(65),
        CATCH(66),
        CHAR(67),
        CLASS(68),
        CONST(69),
        CONTINUE(70),
        _DEFAULT(71),
        DO(72),
        DOUBLE(73),
        ELSE(74),
        ENUM(75),
        EXTENDS(76),
        FALSE(77),
        FINAL(78),
        FINALLY(79),
        FLOAT(80),
        FOR(81),
        GOTO(82),
        IF(83),
        IMPLEMENTS(84),
        IMPORT(85),
        INSTANCEOF(86),
        INT(87),
        INTERFACE(88),
        LONG(89),
        NATIVE(90),
        NEW(91),
        NULL(92),
        PACKAGE(93),
        PRIVATE(94),
        PROTECTED(95),
        PUBLIC(96),
        RETURN(97),
        SHORT(98),
        STATIC(99),
        STRICTFP(100),
        SUPER(101),
        SWITCH(102),
        SYNCHRONIZED(103),
        THIS(104),
        THROW(105),
        THROWS(106),
        TRANSIENT(107),
        TRUE(108),
        TRY(109),
        VOID(110),
        VOLATILE(111),
        WHILE(112),
        YIELD(113),
        REQUIRES(114),
        TO(115),
        WITH(116),
        OPEN(117),
        OPENS(118),
        USES(119),
        MODULE(120),
        EXPORTS(121),
        PROVIDES(122),
        TRANSITIVE(123),
        LONG_LITERAL(124),
        INTEGER_LITERAL(125),
        DECIMAL_LITERAL(126),
        HEX_LITERAL(127),
        OCTAL_LITERAL(128),
        BINARY_LITERAL(129),
        FLOATING_POINT_LITERAL(130),
        DECIMAL_FLOATING_POINT_LITERAL(131),
        DECIMAL_EXPONENT(132),
        HEXADECIMAL_FLOATING_POINT_LITERAL(133),
        HEXADECIMAL_EXPONENT(134),
        HEX_DIGITS(135),
        UNICODE_ESCAPE(136),
        CHARACTER_LITERAL(137),
        STRING_LITERAL(138),
        ENTER_TEXT_BLOCK(139),
        TEXT_BLOCK_LITERAL(140),
        TEXT_BLOCK_CONTENT(141),
        IDENTIFIER(142),
        LETTER(143),
        PART_LETTER(144),
        LPAREN(145),
        RPAREN(146),
        LBRACE(147),
        RBRACE(148),
        LBRACKET(149),
        RBRACKET(150),
        SEMICOLON(151),
        COMMA(152),
        DOT(153),
        AT(154),
        ASSIGN(155),
        LT(156),
        BANG(157),
        TILDE(158),
        HOOK(159),
        COLON(160),
        ARROW(161),
        EQ(162),
        GE(163),
        LE(164),
        NE(165),
        SC_AND(166),
        SC_OR(167),
        INCR(168),
        DECR(169),
        PLUS(170),
        MINUS(171),
        STAR(172),
        SLASH(173),
        BIT_AND(174),
        BIT_OR(175),
        XOR(176),
        REM(177),
        LSHIFT(178),
        PLUSASSIGN(179),
        MINUSASSIGN(180),
        STARASSIGN(181),
        SLASHASSIGN(182),
        ANDASSIGN(183),
        ORASSIGN(184),
        XORASSIGN(185),
        REMASSIGN(186),
        LSHIFTASSIGN(187),
        RSIGNEDSHIFTASSIGN(188),
        RUNSIGNEDSHIFTASSIGN(189),
        ELLIPSIS(190),
        DOUBLECOLON(191),
        RUNSIGNEDSHIFT(192),
        RSIGNEDSHIFT(193),
        GT(194),
        CTRL_Z(195);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 195:
                    return CTRL_Z;
                case 194:
                    return GT;
                case 193:
                    return RSIGNEDSHIFT;
                case 192:
                    return RUNSIGNEDSHIFT;
                case 191:
                    return DOUBLECOLON;
                case 190:
                    return ELLIPSIS;
                case 189:
                    return RUNSIGNEDSHIFTASSIGN;
                case 188:
                    return RSIGNEDSHIFTASSIGN;
                case 187:
                    return LSHIFTASSIGN;
                case 186:
                    return REMASSIGN;
                case 185:
                    return XORASSIGN;
                case 184:
                    return ORASSIGN;
                case 183:
                    return ANDASSIGN;
                case 182:
                    return SLASHASSIGN;
                case 181:
                    return STARASSIGN;
                case 180:
                    return MINUSASSIGN;
                case 179:
                    return PLUSASSIGN;
                case 178:
                    return LSHIFT;
                case 177:
                    return REM;
                case 176:
                    return XOR;
                case 175:
                    return BIT_OR;
                case 174:
                    return BIT_AND;
                case 173:
                    return SLASH;
                case 172:
                    return STAR;
                case 171:
                    return MINUS;
                case 170:
                    return PLUS;
                case 169:
                    return DECR;
                case 168:
                    return INCR;
                case 167:
                    return SC_OR;
                case 166:
                    return SC_AND;
                case 165:
                    return NE;
                case 164:
                    return LE;
                case 163:
                    return GE;
                case 162:
                    return EQ;
                case 161:
                    return ARROW;
                case 160:
                    return COLON;
                case 159:
                    return HOOK;
                case 158:
                    return TILDE;
                case 157:
                    return BANG;
                case 156:
                    return LT;
                case 155:
                    return ASSIGN;
                case 154:
                    return AT;
                case 153:
                    return DOT;
                case 152:
                    return COMMA;
                case 151:
                    return SEMICOLON;
                case 150:
                    return RBRACKET;
                case 149:
                    return LBRACKET;
                case 148:
                    return RBRACE;
                case 147:
                    return LBRACE;
                case 146:
                    return RPAREN;
                case 145:
                    return LPAREN;
                case 144:
                    return PART_LETTER;
                case 143:
                    return LETTER;
                case 142:
                    return IDENTIFIER;
                case 141:
                    return TEXT_BLOCK_CONTENT;
                case 140:
                    return TEXT_BLOCK_LITERAL;
                case 139:
                    return ENTER_TEXT_BLOCK;
                case 138:
                    return STRING_LITERAL;
                case 137:
                    return CHARACTER_LITERAL;
                case 136:
                    return UNICODE_ESCAPE;
                case 135:
                    return HEX_DIGITS;
                case 134:
                    return HEXADECIMAL_EXPONENT;
                case 133:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 132:
                    return DECIMAL_EXPONENT;
                case 131:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 130:
                    return FLOATING_POINT_LITERAL;
                case 129:
                    return BINARY_LITERAL;
                case 128:
                    return OCTAL_LITERAL;
                case 127:
                    return HEX_LITERAL;
                case 126:
                    return DECIMAL_LITERAL;
                case 125:
                    return INTEGER_LITERAL;
                case 124:
                    return LONG_LITERAL;
                case 123:
                    return TRANSITIVE;
                case 122:
                    return PROVIDES;
                case 121:
                    return EXPORTS;
                case 120:
                    return MODULE;
                case 119:
                    return USES;
                case 118:
                    return OPENS;
                case 117:
                    return OPEN;
                case 116:
                    return WITH;
                case 115:
                    return TO;
                case 114:
                    return REQUIRES;
                case 113:
                    return YIELD;
                case 112:
                    return WHILE;
                case 111:
                    return VOLATILE;
                case 110:
                    return VOID;
                case 109:
                    return TRY;
                case 108:
                    return TRUE;
                case 107:
                    return TRANSIENT;
                case 106:
                    return THROWS;
                case 105:
                    return THROW;
                case 104:
                    return THIS;
                case 103:
                    return SYNCHRONIZED;
                case 102:
                    return SWITCH;
                case 101:
                    return SUPER;
                case 100:
                    return STRICTFP;
                case 99:
                    return STATIC;
                case 98:
                    return SHORT;
                case 97:
                    return RETURN;
                case 96:
                    return PUBLIC;
                case 95:
                    return PROTECTED;
                case 94:
                    return PRIVATE;
                case 93:
                    return PACKAGE;
                case 92:
                    return NULL;
                case 91:
                    return NEW;
                case 90:
                    return NATIVE;
                case 89:
                    return LONG;
                case 88:
                    return INTERFACE;
                case 87:
                    return INT;
                case 86:
                    return INSTANCEOF;
                case 85:
                    return IMPORT;
                case 84:
                    return IMPLEMENTS;
                case 83:
                    return IF;
                case 82:
                    return GOTO;
                case 81:
                    return FOR;
                case 80:
                    return FLOAT;
                case 79:
                    return FINALLY;
                case 78:
                    return FINAL;
                case 77:
                    return FALSE;
                case 76:
                    return EXTENDS;
                case 75:
                    return ENUM;
                case 74:
                    return ELSE;
                case 73:
                    return DOUBLE;
                case 72:
                    return DO;
                case 71:
                    return _DEFAULT;
                case 70:
                    return CONTINUE;
                case 69:
                    return CONST;
                case 68:
                    return CLASS;
                case 67:
                    return CHAR;
                case 66:
                    return CATCH;
                case 65:
                    return CASE;
                case 64:
                    return BYTE;
                case 63:
                    return BREAK;
                case 62:
                    return BOOLEAN;
                case 61:
                    return ASSERT;
                case 60:
                    return ABSTRACT;
                case 59:
                    return COMMENT_CONTENT;
                case 58:
                    return MULTI_LINE_COMMENT;
                case 57:
                    return JAVADOC_COMMENT;
                case 56:
                    return ENTER_MULTILINE_COMMENT;
                case 55:
                    return ENTER_JAVADOC_COMMENT;
                case 54:
                    return INSTANCE;
                case 53:
                    return SIGNALS;
                case 52:
                    return NEW_OBJECT;
                case 51:
                    return ERASES;
                case 50:
                    return DECLASSIFIES;
                case 49:
                    return BY;
                case 48:
                    return DETERMINES;
                case 47:
                    return MEASURED_BY;
                case 46:
                    return EXCEPTIONAL_BEHAVIOR;
                case 45:
                    return NORMAL_BEHAVIOR;
                case 44:
                    return BEHAVIOR;
                case 43:
                    return SPEC_PROTECTED;
                case 42:
                    return SPEC_PACKAGE;
                case 41:
                    return SPEC_PRIVATE;
                case 40:
                    return SPEC_PUBLIC;
                case 39:
                    return GHOST;
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
