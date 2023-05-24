/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
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

import com.github.javaparser.ast.Generated;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.CodeGenerationUtils.f;
import static com.github.javaparser.utils.Utils.SYSTEM_EOL;
import static com.github.javaparser.utils.Utils.assertNotNull;

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
        NON_SEALED(43),
        NULL(44),
        PACKAGE(45),
        PERMITS(46),
        PRIVATE(47),
        PROTECTED(48),
        PUBLIC(49),
        RECORD(50),
        RETURN(51),
        SEALED(52),
        SHORT(53),
        STATIC(54),
        STRICTFP(55),
        SUPER(56),
        SWITCH(57),
        SYNCHRONIZED(58),
        THIS(59),
        THROW(60),
        THROWS(61),
        TRANSIENT(62),
        TRUE(63),
        TRY(64),
        VOID(65),
        VOLATILE(66),
        WHILE(67),
        YIELD(68),
        REQUIRES(69),
        TO(70),
        WITH(71),
        OPEN(72),
        OPENS(73),
        USES(74),
        MODULE(75),
        EXPORTS(76),
        PROVIDES(77),
        TRANSITIVE(78),
        SOURCE(79),
        TRANSACTIONBEGIN(80),
        TRANSACTIONCOMMIT(81),
        TRANSACTIONFINISH(82),
        TRANSACTIONABORT(83),
        RETURNTYPE(84),
        SEQ(85),
        SET(86),
        LOOPSCOPE(87),
        MAP(88),
        MERGE_POINT(89),
        METHODFRAME(90),
        LOCSET(91),
        FREE(92),
        EXEC(93),
        CONTINUETYPE(94),
        CCATCH(95),
        CCAT(96),
        BREAKTYPE(97),
        BIGINT(98),
        REAL(99),
        CONTEXTSTART(100),
        TYPEOF(101),
        SWITCHTOIF(102),
        UNPACK(103),
        REATTACHLOOPINVARIANT(104),
        FORINITUNFOLDTRANSFORMER(105),
        LOOPSCOPEINVARIANTTRANSFORMER(106),
        SETSV(107),
        ISSTATIC(108),
        EVALARGS(109),
        REPLACEARGS(110),
        UNWINDLOOP(111),
        CATCHALL(112),
        BEGIN(113),
        COMMIT(114),
        FINISH(115),
        ABORT(116),
        UNWIND_LOOP_BOUNDED(117),
        FORTOWHILE(118),
        DOBREAK(119),
        METHODCALL(120),
        EXPANDMETHODBODY(121),
        CONSTRUCTORCALL(122),
        SPECIALCONSTRUCTORECALL(123),
        POSTWORK(124),
        STATICINITIALIZATION(125),
        RESOLVE_MULTIPLE_VAR_DECL(126),
        ARRAY_POST_DECL(127),
        ARRAY_INIT_CREATION(128),
        ARRAY_INIT_CREATION_TRANSIENT(129),
        ARRAY_INIT_CREATION_ASSIGNMENTS(130),
        ENHANCEDFOR_ELIM(131),
        STATIC_EVALUATE(132),
        CREATE_OBJECT(133),
        LENGTHREF(134),
        GHOST(135),
        MODEL(136),
        TWO_STATE(137),
        NO_STATE(138),
        RESULTARROW(139),
        LONG_LITERAL(140),
        INTEGER_LITERAL(141),
        DECIMAL_LITERAL(142),
        HEX_LITERAL(143),
        OCTAL_LITERAL(144),
        BINARY_LITERAL(145),
        FLOATING_POINT_LITERAL(146),
        DECIMAL_FLOATING_POINT_LITERAL(147),
        DECIMAL_EXPONENT(148),
        HEXADECIMAL_FLOATING_POINT_LITERAL(149),
        HEXADECIMAL_EXPONENT(150),
        HEX_DIGITS(151),
        UNICODE_ESCAPE(152),
        CHARACTER_LITERAL(153),
        STRING_LITERAL(154),
        ENTER_TEXT_BLOCK(155),
        TEXT_BLOCK_LITERAL(156),
        TEXT_BLOCK_CONTENT(157),
        IDENTIFIER(158),
        JMLIDENTIFIER(159),
        SVIDENTIFIER(160),
        KEYIDENTIFIER(161),
        LETTER(162),
        PART_LETTER(163),
        LPAREN(164),
        RPAREN(165),
        LBRACE(166),
        RBRACE(167),
        LBRACKET(168),
        RBRACKET(169),
        SEMICOLON(170),
        COMMA(171),
        DOT(172),
        ELLIPSIS(173),
        AT(174),
        DOUBLECOLON(175),
        ASSIGN(176),
        LT(177),
        BANG(178),
        TILDE(179),
        HOOK(180),
        COLON(181),
        ARROW(182),
        EQ(183),
        GE(184),
        LE(185),
        NE(186),
        SC_AND(187),
        SC_OR(188),
        INCR(189),
        DECR(190),
        PLUS(191),
        MINUS(192),
        STAR(193),
        SLASH(194),
        BIT_AND(195),
        BIT_OR(196),
        XOR(197),
        REM(198),
        LSHIFT(199),
        SHARP(200),
        PLUSASSIGN(201),
        MINUSASSIGN(202),
        STARASSIGN(203),
        SLASHASSIGN(204),
        ANDASSIGN(205),
        ORASSIGN(206),
        XORASSIGN(207),
        REMASSIGN(208),
        LSHIFTASSIGN(209),
        RSIGNEDSHIFTASSIGN(210),
        RUNSIGNEDSHIFTASSIGN(211),
        RUNSIGNEDSHIFT(212),
        RSIGNEDSHIFT(213),
        GT(214),
        CTRL_Z(215);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 215:
                    return CTRL_Z;
                case 214:
                    return GT;
                case 213:
                    return RSIGNEDSHIFT;
                case 212:
                    return RUNSIGNEDSHIFT;
                case 211:
                    return RUNSIGNEDSHIFTASSIGN;
                case 210:
                    return RSIGNEDSHIFTASSIGN;
                case 209:
                    return LSHIFTASSIGN;
                case 208:
                    return REMASSIGN;
                case 207:
                    return XORASSIGN;
                case 206:
                    return ORASSIGN;
                case 205:
                    return ANDASSIGN;
                case 204:
                    return SLASHASSIGN;
                case 203:
                    return STARASSIGN;
                case 202:
                    return MINUSASSIGN;
                case 201:
                    return PLUSASSIGN;
                case 200:
                    return SHARP;
                case 199:
                    return LSHIFT;
                case 198:
                    return REM;
                case 197:
                    return XOR;
                case 196:
                    return BIT_OR;
                case 195:
                    return BIT_AND;
                case 194:
                    return SLASH;
                case 193:
                    return STAR;
                case 192:
                    return MINUS;
                case 191:
                    return PLUS;
                case 190:
                    return DECR;
                case 189:
                    return INCR;
                case 188:
                    return SC_OR;
                case 187:
                    return SC_AND;
                case 186:
                    return NE;
                case 185:
                    return LE;
                case 184:
                    return GE;
                case 183:
                    return EQ;
                case 182:
                    return ARROW;
                case 181:
                    return COLON;
                case 180:
                    return HOOK;
                case 179:
                    return TILDE;
                case 178:
                    return BANG;
                case 177:
                    return LT;
                case 176:
                    return ASSIGN;
                case 175:
                    return DOUBLECOLON;
                case 174:
                    return AT;
                case 173:
                    return ELLIPSIS;
                case 172:
                    return DOT;
                case 171:
                    return COMMA;
                case 170:
                    return SEMICOLON;
                case 169:
                    return RBRACKET;
                case 168:
                    return LBRACKET;
                case 167:
                    return RBRACE;
                case 166:
                    return LBRACE;
                case 165:
                    return RPAREN;
                case 164:
                    return LPAREN;
                case 163:
                    return PART_LETTER;
                case 162:
                    return LETTER;
                case 161:
                    return KEYIDENTIFIER;
                case 160:
                    return SVIDENTIFIER;
                case 159:
                    return JMLIDENTIFIER;
                case 158:
                    return IDENTIFIER;
                case 157:
                    return TEXT_BLOCK_CONTENT;
                case 156:
                    return TEXT_BLOCK_LITERAL;
                case 155:
                    return ENTER_TEXT_BLOCK;
                case 154:
                    return STRING_LITERAL;
                case 153:
                    return CHARACTER_LITERAL;
                case 152:
                    return UNICODE_ESCAPE;
                case 151:
                    return HEX_DIGITS;
                case 150:
                    return HEXADECIMAL_EXPONENT;
                case 149:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 148:
                    return DECIMAL_EXPONENT;
                case 147:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 146:
                    return FLOATING_POINT_LITERAL;
                case 145:
                    return BINARY_LITERAL;
                case 144:
                    return OCTAL_LITERAL;
                case 143:
                    return HEX_LITERAL;
                case 142:
                    return DECIMAL_LITERAL;
                case 141:
                    return INTEGER_LITERAL;
                case 140:
                    return LONG_LITERAL;
                case 139:
                    return RESULTARROW;
                case 138:
                    return NO_STATE;
                case 137:
                    return TWO_STATE;
                case 136:
                    return MODEL;
                case 135:
                    return GHOST;
                case 134:
                    return LENGTHREF;
                case 133:
                    return CREATE_OBJECT;
                case 132:
                    return STATIC_EVALUATE;
                case 131:
                    return ENHANCEDFOR_ELIM;
                case 130:
                    return ARRAY_INIT_CREATION_ASSIGNMENTS;
                case 129:
                    return ARRAY_INIT_CREATION_TRANSIENT;
                case 128:
                    return ARRAY_INIT_CREATION;
                case 127:
                    return ARRAY_POST_DECL;
                case 126:
                    return RESOLVE_MULTIPLE_VAR_DECL;
                case 125:
                    return STATICINITIALIZATION;
                case 124:
                    return POSTWORK;
                case 123:
                    return SPECIALCONSTRUCTORECALL;
                case 122:
                    return CONSTRUCTORCALL;
                case 121:
                    return EXPANDMETHODBODY;
                case 120:
                    return METHODCALL;
                case 119:
                    return DOBREAK;
                case 118:
                    return FORTOWHILE;
                case 117:
                    return UNWIND_LOOP_BOUNDED;
                case 116:
                    return ABORT;
                case 115:
                    return FINISH;
                case 114:
                    return COMMIT;
                case 113:
                    return BEGIN;
                case 112:
                    return CATCHALL;
                case 111:
                    return UNWINDLOOP;
                case 110:
                    return REPLACEARGS;
                case 109:
                    return EVALARGS;
                case 108:
                    return ISSTATIC;
                case 107:
                    return SETSV;
                case 106:
                    return LOOPSCOPEINVARIANTTRANSFORMER;
                case 105:
                    return FORINITUNFOLDTRANSFORMER;
                case 104:
                    return REATTACHLOOPINVARIANT;
                case 103:
                    return UNPACK;
                case 102:
                    return SWITCHTOIF;
                case 101:
                    return TYPEOF;
                case 100:
                    return CONTEXTSTART;
                case 99:
                    return REAL;
                case 98:
                    return BIGINT;
                case 97:
                    return BREAKTYPE;
                case 96:
                    return CCAT;
                case 95:
                    return CCATCH;
                case 94:
                    return CONTINUETYPE;
                case 93:
                    return EXEC;
                case 92:
                    return FREE;
                case 91:
                    return LOCSET;
                case 90:
                    return METHODFRAME;
                case 89:
                    return MERGE_POINT;
                case 88:
                    return MAP;
                case 87:
                    return LOOPSCOPE;
                case 86:
                    return SET;
                case 85:
                    return SEQ;
                case 84:
                    return RETURNTYPE;
                case 83:
                    return TRANSACTIONABORT;
                case 82:
                    return TRANSACTIONFINISH;
                case 81:
                    return TRANSACTIONCOMMIT;
                case 80:
                    return TRANSACTIONBEGIN;
                case 79:
                    return SOURCE;
                case 78:
                    return TRANSITIVE;
                case 77:
                    return PROVIDES;
                case 76:
                    return EXPORTS;
                case 75:
                    return MODULE;
                case 74:
                    return USES;
                case 73:
                    return OPENS;
                case 72:
                    return OPEN;
                case 71:
                    return WITH;
                case 70:
                    return TO;
                case 69:
                    return REQUIRES;
                case 68:
                    return YIELD;
                case 67:
                    return WHILE;
                case 66:
                    return VOLATILE;
                case 65:
                    return VOID;
                case 64:
                    return TRY;
                case 63:
                    return TRUE;
                case 62:
                    return TRANSIENT;
                case 61:
                    return THROWS;
                case 60:
                    return THROW;
                case 59:
                    return THIS;
                case 58:
                    return SYNCHRONIZED;
                case 57:
                    return SWITCH;
                case 56:
                    return SUPER;
                case 55:
                    return STRICTFP;
                case 54:
                    return STATIC;
                case 53:
                    return SHORT;
                case 52:
                    return SEALED;
                case 51:
                    return RETURN;
                case 50:
                    return RECORD;
                case 49:
                    return PUBLIC;
                case 48:
                    return PROTECTED;
                case 47:
                    return PRIVATE;
                case 46:
                    return PERMITS;
                case 45:
                    return PACKAGE;
                case 44:
                    return NULL;
                case 43:
                    return NON_SEALED;
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
