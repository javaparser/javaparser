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
        ASSIGNABLE(16),
        MODIFIABLE(17),
        MODIFIES(18),
        ACCESSIBLE(19),
        REPRESENTS(20),
        NESTED_CONTRACT_START(21),
        NESTED_CONTRACT_END(22),
        ALSO(23),
        PURE(24),
        STRICTLY_PURE(25),
        MODEL(26),
        HELPER(27),
        NULLABLE_BY_DEFAULT(28),
        NON_NULL(29),
        NULLABLE(30),
        BEHAVIOR(31),
        NORMAL_BEHAVIOR(32),
        EXCEPTIONAL_BEHAVIOR(33),
        MEASURED_BY(34),
        DETERMINES(35),
        BY(36),
        DECLASSIFIES(37),
        ERASES(38),
        NEW_OBJECT(39),
        SIGNALS(40),
        INSTANCE(41),
        ENTER_JAVADOC_COMMENT(42),
        ENTER_MULTILINE_COMMENT(43),
        JAVADOC_COMMENT(44),
        MULTI_LINE_COMMENT(45),
        COMMENT_CONTENT(46),
        ABSTRACT(47),
        ASSERT(48),
        BOOLEAN(49),
        BREAK(50),
        BYTE(51),
        CASE(52),
        CATCH(53),
        CHAR(54),
        CLASS(55),
        CONST(56),
        CONTINUE(57),
        _DEFAULT(58),
        DO(59),
        DOUBLE(60),
        ELSE(61),
        ENUM(62),
        EXTENDS(63),
        FALSE(64),
        FINAL(65),
        FINALLY(66),
        FLOAT(67),
        FOR(68),
        GOTO(69),
        IF(70),
        IMPLEMENTS(71),
        IMPORT(72),
        INSTANCEOF(73),
        INT(74),
        INTERFACE(75),
        LONG(76),
        NATIVE(77),
        NEW(78),
        NULL(79),
        PACKAGE(80),
        PRIVATE(81),
        PROTECTED(82),
        PUBLIC(83),
        RETURN(84),
        SHORT(85),
        STATIC(86),
        STRICTFP(87),
        SUPER(88),
        SWITCH(89),
        SYNCHRONIZED(90),
        THIS(91),
        THROW(92),
        THROWS(93),
        TRANSIENT(94),
        TRUE(95),
        TRY(96),
        VOID(97),
        VOLATILE(98),
        WHILE(99),
        YIELD(100),
        REQUIRES(101),
        TO(102),
        WITH(103),
        OPEN(104),
        OPENS(105),
        USES(106),
        MODULE(107),
        EXPORTS(108),
        PROVIDES(109),
        TRANSITIVE(110),
        LONG_LITERAL(111),
        INTEGER_LITERAL(112),
        DECIMAL_LITERAL(113),
        HEX_LITERAL(114),
        OCTAL_LITERAL(115),
        BINARY_LITERAL(116),
        FLOATING_POINT_LITERAL(117),
        DECIMAL_FLOATING_POINT_LITERAL(118),
        DECIMAL_EXPONENT(119),
        HEXADECIMAL_FLOATING_POINT_LITERAL(120),
        HEXADECIMAL_EXPONENT(121),
        HEX_DIGITS(122),
        UNICODE_ESCAPE(123),
        CHARACTER_LITERAL(124),
        STRING_LITERAL(125),
        ENTER_TEXT_BLOCK(126),
        TEXT_BLOCK_LITERAL(127),
        TEXT_BLOCK_CONTENT(128),
        IDENTIFIER(129),
        LETTER(130),
        PART_LETTER(131),
        LPAREN(132),
        RPAREN(133),
        LBRACE(134),
        RBRACE(135),
        LBRACKET(136),
        RBRACKET(137),
        SEMICOLON(138),
        COMMA(139),
        DOT(140),
        AT(141),
        ASSIGN(142),
        LT(143),
        BANG(144),
        TILDE(145),
        HOOK(146),
        COLON(147),
        ARROW(148),
        EQ(149),
        GE(150),
        LE(151),
        NE(152),
        SC_AND(153),
        SC_OR(154),
        INCR(155),
        DECR(156),
        PLUS(157),
        MINUS(158),
        STAR(159),
        SLASH(160),
        BIT_AND(161),
        BIT_OR(162),
        XOR(163),
        REM(164),
        LSHIFT(165),
        PLUSASSIGN(166),
        MINUSASSIGN(167),
        STARASSIGN(168),
        SLASHASSIGN(169),
        ANDASSIGN(170),
        ORASSIGN(171),
        XORASSIGN(172),
        REMASSIGN(173),
        LSHIFTASSIGN(174),
        RSIGNEDSHIFTASSIGN(175),
        RUNSIGNEDSHIFTASSIGN(176),
        ELLIPSIS(177),
        DOUBLECOLON(178),
        RUNSIGNEDSHIFT(179),
        RSIGNEDSHIFT(180),
        GT(181),
        CTRL_Z(182);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 182:
                    return CTRL_Z;
                case 181:
                    return GT;
                case 180:
                    return RSIGNEDSHIFT;
                case 179:
                    return RUNSIGNEDSHIFT;
                case 178:
                    return DOUBLECOLON;
                case 177:
                    return ELLIPSIS;
                case 176:
                    return RUNSIGNEDSHIFTASSIGN;
                case 175:
                    return RSIGNEDSHIFTASSIGN;
                case 174:
                    return LSHIFTASSIGN;
                case 173:
                    return REMASSIGN;
                case 172:
                    return XORASSIGN;
                case 171:
                    return ORASSIGN;
                case 170:
                    return ANDASSIGN;
                case 169:
                    return SLASHASSIGN;
                case 168:
                    return STARASSIGN;
                case 167:
                    return MINUSASSIGN;
                case 166:
                    return PLUSASSIGN;
                case 165:
                    return LSHIFT;
                case 164:
                    return REM;
                case 163:
                    return XOR;
                case 162:
                    return BIT_OR;
                case 161:
                    return BIT_AND;
                case 160:
                    return SLASH;
                case 159:
                    return STAR;
                case 158:
                    return MINUS;
                case 157:
                    return PLUS;
                case 156:
                    return DECR;
                case 155:
                    return INCR;
                case 154:
                    return SC_OR;
                case 153:
                    return SC_AND;
                case 152:
                    return NE;
                case 151:
                    return LE;
                case 150:
                    return GE;
                case 149:
                    return EQ;
                case 148:
                    return ARROW;
                case 147:
                    return COLON;
                case 146:
                    return HOOK;
                case 145:
                    return TILDE;
                case 144:
                    return BANG;
                case 143:
                    return LT;
                case 142:
                    return ASSIGN;
                case 141:
                    return AT;
                case 140:
                    return DOT;
                case 139:
                    return COMMA;
                case 138:
                    return SEMICOLON;
                case 137:
                    return RBRACKET;
                case 136:
                    return LBRACKET;
                case 135:
                    return RBRACE;
                case 134:
                    return LBRACE;
                case 133:
                    return RPAREN;
                case 132:
                    return LPAREN;
                case 131:
                    return PART_LETTER;
                case 130:
                    return LETTER;
                case 129:
                    return IDENTIFIER;
                case 128:
                    return TEXT_BLOCK_CONTENT;
                case 127:
                    return TEXT_BLOCK_LITERAL;
                case 126:
                    return ENTER_TEXT_BLOCK;
                case 125:
                    return STRING_LITERAL;
                case 124:
                    return CHARACTER_LITERAL;
                case 123:
                    return UNICODE_ESCAPE;
                case 122:
                    return HEX_DIGITS;
                case 121:
                    return HEXADECIMAL_EXPONENT;
                case 120:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 119:
                    return DECIMAL_EXPONENT;
                case 118:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 117:
                    return FLOATING_POINT_LITERAL;
                case 116:
                    return BINARY_LITERAL;
                case 115:
                    return OCTAL_LITERAL;
                case 114:
                    return HEX_LITERAL;
                case 113:
                    return DECIMAL_LITERAL;
                case 112:
                    return INTEGER_LITERAL;
                case 111:
                    return LONG_LITERAL;
                case 110:
                    return TRANSITIVE;
                case 109:
                    return PROVIDES;
                case 108:
                    return EXPORTS;
                case 107:
                    return MODULE;
                case 106:
                    return USES;
                case 105:
                    return OPENS;
                case 104:
                    return OPEN;
                case 103:
                    return WITH;
                case 102:
                    return TO;
                case 101:
                    return REQUIRES;
                case 100:
                    return YIELD;
                case 99:
                    return WHILE;
                case 98:
                    return VOLATILE;
                case 97:
                    return VOID;
                case 96:
                    return TRY;
                case 95:
                    return TRUE;
                case 94:
                    return TRANSIENT;
                case 93:
                    return THROWS;
                case 92:
                    return THROW;
                case 91:
                    return THIS;
                case 90:
                    return SYNCHRONIZED;
                case 89:
                    return SWITCH;
                case 88:
                    return SUPER;
                case 87:
                    return STRICTFP;
                case 86:
                    return STATIC;
                case 85:
                    return SHORT;
                case 84:
                    return RETURN;
                case 83:
                    return PUBLIC;
                case 82:
                    return PROTECTED;
                case 81:
                    return PRIVATE;
                case 80:
                    return PACKAGE;
                case 79:
                    return NULL;
                case 78:
                    return NEW;
                case 77:
                    return NATIVE;
                case 76:
                    return LONG;
                case 75:
                    return INTERFACE;
                case 74:
                    return INT;
                case 73:
                    return INSTANCEOF;
                case 72:
                    return IMPORT;
                case 71:
                    return IMPLEMENTS;
                case 70:
                    return IF;
                case 69:
                    return GOTO;
                case 68:
                    return FOR;
                case 67:
                    return FLOAT;
                case 66:
                    return FINALLY;
                case 65:
                    return FINAL;
                case 64:
                    return FALSE;
                case 63:
                    return EXTENDS;
                case 62:
                    return ENUM;
                case 61:
                    return ELSE;
                case 60:
                    return DOUBLE;
                case 59:
                    return DO;
                case 58:
                    return _DEFAULT;
                case 57:
                    return CONTINUE;
                case 56:
                    return CONST;
                case 55:
                    return CLASS;
                case 54:
                    return CHAR;
                case 53:
                    return CATCH;
                case 52:
                    return CASE;
                case 51:
                    return BYTE;
                case 50:
                    return BREAK;
                case 49:
                    return BOOLEAN;
                case 48:
                    return ASSERT;
                case 47:
                    return ABSTRACT;
                case 46:
                    return COMMENT_CONTENT;
                case 45:
                    return MULTI_LINE_COMMENT;
                case 44:
                    return JAVADOC_COMMENT;
                case 43:
                    return ENTER_MULTILINE_COMMENT;
                case 42:
                    return ENTER_JAVADOC_COMMENT;
                case 41:
                    return INSTANCE;
                case 40:
                    return SIGNALS;
                case 39:
                    return NEW_OBJECT;
                case 38:
                    return ERASES;
                case 37:
                    return DECLASSIFIES;
                case 36:
                    return BY;
                case 35:
                    return DETERMINES;
                case 34:
                    return MEASURED_BY;
                case 33:
                    return EXCEPTIONAL_BEHAVIOR;
                case 32:
                    return NORMAL_BEHAVIOR;
                case 31:
                    return BEHAVIOR;
                case 30:
                    return NULLABLE;
                case 29:
                    return NON_NULL;
                case 28:
                    return NULLABLE_BY_DEFAULT;
                case 27:
                    return HELPER;
                case 26:
                    return MODEL;
                case 25:
                    return STRICTLY_PURE;
                case 24:
                    return PURE;
                case 23:
                    return ALSO;
                case 22:
                    return NESTED_CONTRACT_END;
                case 21:
                    return NESTED_CONTRACT_START;
                case 20:
                    return REPRESENTS;
                case 19:
                    return ACCESSIBLE;
                case 18:
                    return MODIFIES;
                case 17:
                    return MODIFIABLE;
                case 16:
                    return ASSIGNABLE;
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
