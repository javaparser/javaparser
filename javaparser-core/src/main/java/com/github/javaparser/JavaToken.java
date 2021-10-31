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
        CCAT(92),
        BREAKTYPE(93),
        BIGINT(94),
        REAL(95),
        CONTEXTSTART(96),
        TYPEOF(97),
        SWITCHTOIF(98),
        UNPACK(99),
        REATTACHLOOPINVARIANT(100),
        FORINITUNFOLDTRANSFORMER(101),
        LOOPSCOPEINVARIANTTRANSFORMER(102),
        SETSV(103),
        ISSTATIC(104),
        EVALARGS(105),
        REPLACEARGS(106),
        UNWINDLOOP(107),
        CATCHALL(108),
        BEGIN(109),
        COMMIT(110),
        FINISH(111),
        ABORT(112),
        UNWIND_LOOP_BOUNDED(113),
        FORTOWHILE(114),
        DOBREAK(115),
        METHODCALL(116),
        EXPANDMETHODBODY(117),
        CONSTRUCTORCALL(118),
        SPECIALCONSTRUCTORECALL(119),
        POSTWORK(120),
        STATICINITIALIZATION(121),
        RESOLVE_MULTIPLE_VAR_DECL(122),
        ARRAY_POST_DECL(123),
        ARRAY_INIT_CREATION(124),
        ARRAY_INIT_CREATION_TRANSIENT(125),
        ARRAY_INIT_CREATION_ASSIGNMENTS(126),
        ENHANCEDFOR_ELIM(127),
        STATIC_EVALUATE(128),
        CREATE_OBJECT(129),
        LENGTHREF(130),
        GHOST(131),
        MODEL(132),
        LONG_LITERAL(133),
        INTEGER_LITERAL(134),
        DECIMAL_LITERAL(135),
        HEX_LITERAL(136),
        OCTAL_LITERAL(137),
        BINARY_LITERAL(138),
        FLOATING_POINT_LITERAL(139),
        DECIMAL_FLOATING_POINT_LITERAL(140),
        DECIMAL_EXPONENT(141),
        HEXADECIMAL_FLOATING_POINT_LITERAL(142),
        HEXADECIMAL_EXPONENT(143),
        HEX_DIGITS(144),
        UNICODE_ESCAPE(145),
        CHARACTER_LITERAL(146),
        STRING_LITERAL(147),
        ENTER_TEXT_BLOCK(148),
        TEXT_BLOCK_LITERAL(149),
        TEXT_BLOCK_CONTENT(150),
        IDENTIFIER(151),
        JMLIDENTIFIER(152),
        SVIDENTIFIER(153),
        LETTER(154),
        PART_LETTER(155),
        LPAREN(156),
        RPAREN(157),
        LBRACE(158),
        RBRACE(159),
        LBRACKET(160),
        RBRACKET(161),
        SEMICOLON(162),
        COMMA(163),
        DOT(164),
        ELLIPSIS(165),
        AT(166),
        DOUBLECOLON(167),
        ASSIGN(168),
        LT(169),
        BANG(170),
        TILDE(171),
        HOOK(172),
        COLON(173),
        ARROW(174),
        EQ(175),
        GE(176),
        LE(177),
        NE(178),
        SC_AND(179),
        SC_OR(180),
        INCR(181),
        DECR(182),
        PLUS(183),
        MINUS(184),
        STAR(185),
        SLASH(186),
        BIT_AND(187),
        BIT_OR(188),
        XOR(189),
        REM(190),
        LSHIFT(191),
        SHARP(192),
        PLUSASSIGN(193),
        MINUSASSIGN(194),
        STARASSIGN(195),
        SLASHASSIGN(196),
        ANDASSIGN(197),
        ORASSIGN(198),
        XORASSIGN(199),
        REMASSIGN(200),
        LSHIFTASSIGN(201),
        RSIGNEDSHIFTASSIGN(202),
        RUNSIGNEDSHIFTASSIGN(203),
        RUNSIGNEDSHIFT(204),
        RSIGNEDSHIFT(205),
        GT(206),
        CTRL_Z(207);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 207:
                    return CTRL_Z;
                case 206:
                    return GT;
                case 205:
                    return RSIGNEDSHIFT;
                case 204:
                    return RUNSIGNEDSHIFT;
                case 203:
                    return RUNSIGNEDSHIFTASSIGN;
                case 202:
                    return RSIGNEDSHIFTASSIGN;
                case 201:
                    return LSHIFTASSIGN;
                case 200:
                    return REMASSIGN;
                case 199:
                    return XORASSIGN;
                case 198:
                    return ORASSIGN;
                case 197:
                    return ANDASSIGN;
                case 196:
                    return SLASHASSIGN;
                case 195:
                    return STARASSIGN;
                case 194:
                    return MINUSASSIGN;
                case 193:
                    return PLUSASSIGN;
                case 192:
                    return SHARP;
                case 191:
                    return LSHIFT;
                case 190:
                    return REM;
                case 189:
                    return XOR;
                case 188:
                    return BIT_OR;
                case 187:
                    return BIT_AND;
                case 186:
                    return SLASH;
                case 185:
                    return STAR;
                case 184:
                    return MINUS;
                case 183:
                    return PLUS;
                case 182:
                    return DECR;
                case 181:
                    return INCR;
                case 180:
                    return SC_OR;
                case 179:
                    return SC_AND;
                case 178:
                    return NE;
                case 177:
                    return LE;
                case 176:
                    return GE;
                case 175:
                    return EQ;
                case 174:
                    return ARROW;
                case 173:
                    return COLON;
                case 172:
                    return HOOK;
                case 171:
                    return TILDE;
                case 170:
                    return BANG;
                case 169:
                    return LT;
                case 168:
                    return ASSIGN;
                case 167:
                    return DOUBLECOLON;
                case 166:
                    return AT;
                case 165:
                    return ELLIPSIS;
                case 164:
                    return DOT;
                case 163:
                    return COMMA;
                case 162:
                    return SEMICOLON;
                case 161:
                    return RBRACKET;
                case 160:
                    return LBRACKET;
                case 159:
                    return RBRACE;
                case 158:
                    return LBRACE;
                case 157:
                    return RPAREN;
                case 156:
                    return LPAREN;
                case 155:
                    return PART_LETTER;
                case 154:
                    return LETTER;
                case 153:
                    return SVIDENTIFIER;
                case 152:
                    return JMLIDENTIFIER;
                case 151:
                    return IDENTIFIER;
                case 150:
                    return TEXT_BLOCK_CONTENT;
                case 149:
                    return TEXT_BLOCK_LITERAL;
                case 148:
                    return ENTER_TEXT_BLOCK;
                case 147:
                    return STRING_LITERAL;
                case 146:
                    return CHARACTER_LITERAL;
                case 145:
                    return UNICODE_ESCAPE;
                case 144:
                    return HEX_DIGITS;
                case 143:
                    return HEXADECIMAL_EXPONENT;
                case 142:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 141:
                    return DECIMAL_EXPONENT;
                case 140:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 139:
                    return FLOATING_POINT_LITERAL;
                case 138:
                    return BINARY_LITERAL;
                case 137:
                    return OCTAL_LITERAL;
                case 136:
                    return HEX_LITERAL;
                case 135:
                    return DECIMAL_LITERAL;
                case 134:
                    return INTEGER_LITERAL;
                case 133:
                    return LONG_LITERAL;
                case 132:
                    return MODEL;
                case 131:
                    return GHOST;
                case 130:
                    return LENGTHREF;
                case 129:
                    return CREATE_OBJECT;
                case 128:
                    return STATIC_EVALUATE;
                case 127:
                    return ENHANCEDFOR_ELIM;
                case 126:
                    return ARRAY_INIT_CREATION_ASSIGNMENTS;
                case 125:
                    return ARRAY_INIT_CREATION_TRANSIENT;
                case 124:
                    return ARRAY_INIT_CREATION;
                case 123:
                    return ARRAY_POST_DECL;
                case 122:
                    return RESOLVE_MULTIPLE_VAR_DECL;
                case 121:
                    return STATICINITIALIZATION;
                case 120:
                    return POSTWORK;
                case 119:
                    return SPECIALCONSTRUCTORECALL;
                case 118:
                    return CONSTRUCTORCALL;
                case 117:
                    return EXPANDMETHODBODY;
                case 116:
                    return METHODCALL;
                case 115:
                    return DOBREAK;
                case 114:
                    return FORTOWHILE;
                case 113:
                    return UNWIND_LOOP_BOUNDED;
                case 112:
                    return ABORT;
                case 111:
                    return FINISH;
                case 110:
                    return COMMIT;
                case 109:
                    return BEGIN;
                case 108:
                    return CATCHALL;
                case 107:
                    return UNWINDLOOP;
                case 106:
                    return REPLACEARGS;
                case 105:
                    return EVALARGS;
                case 104:
                    return ISSTATIC;
                case 103:
                    return SETSV;
                case 102:
                    return LOOPSCOPEINVARIANTTRANSFORMER;
                case 101:
                    return FORINITUNFOLDTRANSFORMER;
                case 100:
                    return REATTACHLOOPINVARIANT;
                case 99:
                    return UNPACK;
                case 98:
                    return SWITCHTOIF;
                case 97:
                    return TYPEOF;
                case 96:
                    return CONTEXTSTART;
                case 95:
                    return REAL;
                case 94:
                    return BIGINT;
                case 93:
                    return BREAKTYPE;
                case 92:
                    return CCAT;
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
