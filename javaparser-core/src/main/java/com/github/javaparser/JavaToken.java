/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Generated;
import com.github.javaparser.utils.LineSeparator;
import java.util.List;
import java.util.Optional;

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
        // ___   -> recognized as ">>>", then ">>" put back in the stream but Token(type=GT, image=">>>") passed to this
        // class
        // ___  -> recognized as ">>>", then ">>" put back in the stream but Token(type=GT, image=">>>") passed to this
        // class
        // __  -> recognized as ">>", then ">" put back in the stream but Token(type=GT, image=">>") passed to this
        // class
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
            content = LineSeparator.SYSTEM.asRawString();
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
        WHEN(79),
        SOURCE(80),
        TRANSACTIONBEGIN(81),
        TRANSACTIONCOMMIT(82),
        TRANSACTIONFINISH(83),
        TRANSACTIONABORT(84),
        RETURNTYPE(85),
        LOOPSCOPE(86),
        MERGE_POINT(87),
        METHODFRAME(88),
        EXEC(89),
        CONTINUETYPE(90),
        CCATCH(91),
        CCAT(92),
        BREAKTYPE(93),
        CONTEXTSTART(94),
        TYPEOF(95),
        SWITCHTOIF(96),
        UNPACK(97),
        REATTACHLOOPINVARIANT(98),
        FORINITUNFOLDTRANSFORMER(99),
        LOOPSCOPEINVARIANTTRANSFORMER(100),
        SETSV(101),
        ISSTATIC(102),
        EVALARGS(103),
        REPLACEARGS(104),
        UNWINDLOOP(105),
        CATCHALL(106),
        BEGIN(107),
        COMMIT(108),
        FINISH(109),
        ABORT(110),
        UNWIND_LOOP_BOUNDED(111),
        FORTOWHILE(112),
        DOBREAK(113),
        METHODCALL(114),
        EXPANDMETHODBODY(115),
        CONSTRUCTORCALL(116),
        SPECIALCONSTRUCTORECALL(117),
        POSTWORK(118),
        STATICINITIALIZATION(119),
        RESOLVE_MULTIPLE_VAR_DECL(120),
        ARRAY_POST_DECL(121),
        ARRAY_INIT_CREATION(122),
        ARRAY_INIT_CREATION_TRANSIENT(123),
        ARRAY_INIT_CREATION_ASSIGNMENTS(124),
        ENHANCEDFOR_ELIM(125),
        STATIC_EVALUATE(126),
        CREATE_OBJECT(127),
        LENGTHREF(128),
        GHOST(129),
        MODEL(130),
        TWO_STATE(131),
        NO_STATE(132),
        RESULTARROW(133),
        LONG_LITERAL(134),
        INTEGER_LITERAL(135),
        DECIMAL_LITERAL(136),
        HEX_LITERAL(137),
        OCTAL_LITERAL(138),
        BINARY_LITERAL(139),
        FLOATING_POINT_LITERAL(140),
        DECIMAL_FLOATING_POINT_LITERAL(141),
        DECIMAL_EXPONENT(142),
        HEXADECIMAL_FLOATING_POINT_LITERAL(143),
        HEXADECIMAL_EXPONENT(144),
        HEX_DIGITS(145),
        UNICODE_ESCAPE(146),
        CHARACTER_LITERAL(147),
        STRING_LITERAL(148),
        ENTER_TEXT_BLOCK(149),
        TEXT_BLOCK_LITERAL(150),
        TEXT_BLOCK_CONTENT(151),
        IDENTIFIER(152),
        JMLIDENTIFIER(153),
        SVIDENTIFIER(154),
        KEYIDENTIFIER(155),
        NON_UNDERSCORE_LETTER(156),
        PART_LETTER(157),
        LPAREN(158),
        RPAREN(159),
        LBRACE(160),
        RBRACE(161),
        LBRACKET(162),
        RBRACKET(163),
        SEMICOLON(164),
        COMMA(165),
        DOT(166),
        ELLIPSIS(167),
        AT(168),
        DOUBLECOLON(169),
        ASSIGN(170),
        LT(171),
        BANG(172),
        TILDE(173),
        HOOK(174),
        COLON(175),
        ARROW(176),
        EQ(177),
        GE(178),
        LE(179),
        NE(180),
        SC_AND(181),
        SC_OR(182),
        INCR(183),
        DECR(184),
        PLUS(185),
        MINUS(186),
        STAR(187),
        SLASH(188),
        BIT_AND(189),
        BIT_OR(190),
        XOR(191),
        REM(192),
        LSHIFT(193),
        SHARP(194),
        PLUSASSIGN(195),
        MINUSASSIGN(196),
        STARASSIGN(197),
        SLASHASSIGN(198),
        ANDASSIGN(199),
        ORASSIGN(200),
        XORASSIGN(201),
        REMASSIGN(202),
        LSHIFTASSIGN(203),
        RSIGNEDSHIFTASSIGN(204),
        RUNSIGNEDSHIFTASSIGN(205),
        RUNSIGNEDSHIFT(206),
        RSIGNEDSHIFT(207),
        GT(208),
        CTRL_Z(209),
        UNNAMED_PLACEHOLDER(210);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 210:
                    return UNNAMED_PLACEHOLDER;
                case 209:
                    return CTRL_Z;
                case 208:
                    return GT;
                case 207:
                    return RSIGNEDSHIFT;
                case 206:
                    return RUNSIGNEDSHIFT;
                case 205:
                    return RUNSIGNEDSHIFTASSIGN;
                case 204:
                    return RSIGNEDSHIFTASSIGN;
                case 203:
                    return LSHIFTASSIGN;
                case 202:
                    return REMASSIGN;
                case 201:
                    return XORASSIGN;
                case 200:
                    return ORASSIGN;
                case 199:
                    return ANDASSIGN;
                case 198:
                    return SLASHASSIGN;
                case 197:
                    return STARASSIGN;
                case 196:
                    return MINUSASSIGN;
                case 195:
                    return PLUSASSIGN;
                case 194:
                    return SHARP;
                case 193:
                    return LSHIFT;
                case 192:
                    return REM;
                case 191:
                    return XOR;
                case 190:
                    return BIT_OR;
                case 189:
                    return BIT_AND;
                case 188:
                    return SLASH;
                case 187:
                    return STAR;
                case 186:
                    return MINUS;
                case 185:
                    return PLUS;
                case 184:
                    return DECR;
                case 183:
                    return INCR;
                case 182:
                    return SC_OR;
                case 181:
                    return SC_AND;
                case 180:
                    return NE;
                case 179:
                    return LE;
                case 178:
                    return GE;
                case 177:
                    return EQ;
                case 176:
                    return ARROW;
                case 175:
                    return COLON;
                case 174:
                    return HOOK;
                case 173:
                    return TILDE;
                case 172:
                    return BANG;
                case 171:
                    return LT;
                case 170:
                    return ASSIGN;
                case 169:
                    return DOUBLECOLON;
                case 168:
                    return AT;
                case 167:
                    return ELLIPSIS;
                case 166:
                    return DOT;
                case 165:
                    return COMMA;
                case 164:
                    return SEMICOLON;
                case 163:
                    return RBRACKET;
                case 162:
                    return LBRACKET;
                case 161:
                    return RBRACE;
                case 160:
                    return LBRACE;
                case 159:
                    return RPAREN;
                case 158:
                    return LPAREN;
                case 157:
                    return PART_LETTER;
                case 156:
                    return NON_UNDERSCORE_LETTER;
                case 155:
                    return KEYIDENTIFIER;
                case 154:
                    return SVIDENTIFIER;
                case 153:
                    return JMLIDENTIFIER;
                case 152:
                    return IDENTIFIER;
                case 151:
                    return TEXT_BLOCK_CONTENT;
                case 150:
                    return TEXT_BLOCK_LITERAL;
                case 149:
                    return ENTER_TEXT_BLOCK;
                case 148:
                    return STRING_LITERAL;
                case 147:
                    return CHARACTER_LITERAL;
                case 146:
                    return UNICODE_ESCAPE;
                case 145:
                    return HEX_DIGITS;
                case 144:
                    return HEXADECIMAL_EXPONENT;
                case 143:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 142:
                    return DECIMAL_EXPONENT;
                case 141:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 140:
                    return FLOATING_POINT_LITERAL;
                case 139:
                    return BINARY_LITERAL;
                case 138:
                    return OCTAL_LITERAL;
                case 137:
                    return HEX_LITERAL;
                case 136:
                    return DECIMAL_LITERAL;
                case 135:
                    return INTEGER_LITERAL;
                case 134:
                    return LONG_LITERAL;
                case 133:
                    return RESULTARROW;
                case 132:
                    return NO_STATE;
                case 131:
                    return TWO_STATE;
                case 130:
                    return MODEL;
                case 129:
                    return GHOST;
                case 128:
                    return LENGTHREF;
                case 127:
                    return CREATE_OBJECT;
                case 126:
                    return STATIC_EVALUATE;
                case 125:
                    return ENHANCEDFOR_ELIM;
                case 124:
                    return ARRAY_INIT_CREATION_ASSIGNMENTS;
                case 123:
                    return ARRAY_INIT_CREATION_TRANSIENT;
                case 122:
                    return ARRAY_INIT_CREATION;
                case 121:
                    return ARRAY_POST_DECL;
                case 120:
                    return RESOLVE_MULTIPLE_VAR_DECL;
                case 119:
                    return STATICINITIALIZATION;
                case 118:
                    return POSTWORK;
                case 117:
                    return SPECIALCONSTRUCTORECALL;
                case 116:
                    return CONSTRUCTORCALL;
                case 115:
                    return EXPANDMETHODBODY;
                case 114:
                    return METHODCALL;
                case 113:
                    return DOBREAK;
                case 112:
                    return FORTOWHILE;
                case 111:
                    return UNWIND_LOOP_BOUNDED;
                case 110:
                    return ABORT;
                case 109:
                    return FINISH;
                case 108:
                    return COMMIT;
                case 107:
                    return BEGIN;
                case 106:
                    return CATCHALL;
                case 105:
                    return UNWINDLOOP;
                case 104:
                    return REPLACEARGS;
                case 103:
                    return EVALARGS;
                case 102:
                    return ISSTATIC;
                case 101:
                    return SETSV;
                case 100:
                    return LOOPSCOPEINVARIANTTRANSFORMER;
                case 99:
                    return FORINITUNFOLDTRANSFORMER;
                case 98:
                    return REATTACHLOOPINVARIANT;
                case 97:
                    return UNPACK;
                case 96:
                    return SWITCHTOIF;
                case 95:
                    return TYPEOF;
                case 94:
                    return CONTEXTSTART;
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
                    return METHODFRAME;
                case 87:
                    return MERGE_POINT;
                case 86:
                    return LOOPSCOPE;
                case 85:
                    return RETURNTYPE;
                case 84:
                    return TRANSACTIONABORT;
                case 83:
                    return TRANSACTIONFINISH;
                case 82:
                    return TRANSACTIONCOMMIT;
                case 81:
                    return TRANSACTIONBEGIN;
                case 80:
                    return SOURCE;
                case 79:
                    return WHEN;
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
