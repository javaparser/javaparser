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
        AT_AT_BEGINN(1),
        SPACE(2),
        WINDOWS_EOL(3),
        UNIX_EOL(4),
        OLD_MAC_EOL(5),
        SINGLE_LINE_COMMENT_IN_MULTI_JML(6),
        JML_SINGLE_START0(7),
        SINGLE_LINE_COMMENT0(8),
        SINGLE_LINE_COMMENT(9),
        JML_SINGLE_START(10),
        JML_MULTI_START(11),
        JML_MULTI_END(12),
        JML_SINGLE_END(13),
        INVARIANT(14),
        ABRUPT_BEHAVIOR(15),
        ABRUPT_BEHAVIOUR(16),
        MODEL_BEHAVIOR(17),
        MODEL_BEHAVIOUR(18),
        ACCESSIBLE(19),
        ACCESSIBLE_REDUNDANTLY(20),
        ALSO(21),
        ANTIVALENCE(22),
        ASSERT_REDUNDANTLY(23),
        ASSIGNABLE(24),
        ASSIGNABLE_REDUNDANTLY(25),
        ASSUME(26),
        ASSUME_REDUNDANTLY(27),
        AXIOM(28),
        BEHAVIOR(29),
        BEHAVIOUR(30),
        BIGINT(31),
        BIGINT_MATH(32),
        BREAKS(33),
        BREAKS_REDUNDANTLY(34),
        BREAK_BEHAVIOR(35),
        BREAK_BEHAVIOUR(36),
        CALLABLE(37),
        CALLABLE_REDUNDANTLY(38),
        CAPTURES(39),
        CAPTURES_REDUNDANTLY(40),
        CHOOSE(41),
        CHOOSE_IF(42),
        CODE(43),
        CODE_BIGINT_MATH(44),
        CODE_JAVA_MATH(45),
        CODE_SAFE_MATH(46),
        CONSTRAINT(47),
        CONSTRAINT_REDUNDANTLY(48),
        CONSTRUCTOR(49),
        CONTINUES(50),
        CONTINUES_REDUNDANTLY(51),
        CONTINUE_BEHAVIOR(52),
        CONTINUE_BEHAVIOUR(53),
        DECLASSIFIES(54),
        DECREASES(55),
        DECREASES_REDUNDANTLY(56),
        DECREASING(57),
        DECREASING_REDUNDANTLY(58),
        DETERMINES(59),
        DIVERGES(60),
        DIVERGES_REDUNDANTLY(61),
        DURATION(62),
        DURATION_REDUNDANTLY(63),
        ELEMTYPE(64),
        ENSURES(65),
        ENSURES_REDUNDANTLY(66),
        ENSURES_FREE(67),
        REQUIRES_FREE(68),
        EQUIVALENCE(69),
        IMPLICATION(70),
        IMPLICATION_BACKWARD(71),
        ERASES(72),
        EXAMPLE(73),
        EXCEPTIONAL_BEHAVIOR(74),
        EXCEPTIONAL_BEHAVIOUR(75),
        EXCEPTIONAL_EXAMPLE(76),
        EXISTS(77),
        EXSURES(78),
        EXSURES_REDUNDANTLY(79),
        EXTRACT(80),
        FIELD(81),
        FORALLQ(82),
        FORALL(83),
        FOR_EXAMPLE(84),
        GHOST(85),
        HELPER(86),
        HENCE_BY(87),
        HENCE_BY_REDUNDANTLY(88),
        IMPLIES_THAT(89),
        IN(90),
        INITIALIZER(91),
        INITIALLY(92),
        INSTANCE(93),
        TWO_STATE(94),
        NO_STATE(95),
        INVARIANT_REDUNDANTLY(96),
        IN_REDUNDANTLY(97),
        JAVA_MATH(98),
        LOOP_INVARIANT(99),
        LOOP_INVARIANT_REDUNDANTLY(100),
        MAINTAINING(101),
        MAINTAINING_REDUNDANTLY(102),
        MAPS(103),
        MAPS_REDUNDANTLY(104),
        MAX(105),
        MEASURED_BY(106),
        ESC_MEASURED_BY(107),
        MEASURED_BY_REDUNDANTLY(108),
        METHOD(109),
        MIN(110),
        MODEL(111),
        MODEL_PROGRAM(112),
        MODIFIABLE(113),
        MODIFIABLE_REDUNDANTLY(114),
        MODIFIES(115),
        MODIFIES_REDUNDANTLY(116),
        MONITORED(117),
        MONITORS_FOR(118),
        NESTED_CONTRACT_END(119),
        NESTED_CONTRACT_START(120),
        NEW_OBJECT(121),
        NONNULLELEMENTS(122),
        NON_NULL(123),
        NORMAL_BEHAVIOR(124),
        NORMAL_BEHAVIOUR(125),
        NORMAL_EXAMPLE(126),
        NOWARN(127),
        NOWARN_OP(128),
        NULLABLE(129),
        NULLABLE_BY_DEFAULT(130),
        NUM_OF(131),
        OLD(132),
        OR(133),
        POST(134),
        POST_REDUNDANTLY(135),
        PRE_ESC(136),
        PRE(137),
        PRE_REDUNDANTLY(138),
        PRODUCT(139),
        PURE(140),
        REACH(141),
        READABLE(142),
        REAL(143),
        REFINING(144),
        REPRESENTS(145),
        REPRESENTS_REDUNDANTLY(146),
        REQUIRES_REDUNDANTLY(147),
        RESULT(148),
        RETURNS(149),
        RETURNS_REDUNDANTLY(150),
        RETURN_BEHAVIOR(151),
        RETURN_BEHAVIOUR(152),
        SAFE_MATH(153),
        SET(154),
        SIGNALS(155),
        SIGNALS_ONLY(156),
        SIGNALS_ONLY_REDUNDANTLY(157),
        SIGNALS_REDUNDANTLY(158),
        SPEC_BIGINT_MATH(159),
        SPEC_JAVA_MATH(160),
        SPEC_PACKAGE(161),
        SPEC_PRIVATE(162),
        SPEC_PROTECTED(163),
        SPEC_PUBLIC(164),
        SPEC_SAFE_MATH(165),
        STATIC_INITIALIZER(166),
        STRICTLY_PURE(167),
        SUBTYPE(168),
        SUCH_THAT(169),
        SUM(170),
        TYPE(171),
        TYPEOF(172),
        UNINITIALIZED(173),
        UNKNOWN_OP(174),
        UNKNOWN_OP_EQ(175),
        UNREACHABLE(176),
        WARN(177),
        WARN_OP(178),
        WHEN(179),
        WHEN_REDUNDANTLY(180),
        WORKING_SPACE_ESC(181),
        WORKING_SPACE(182),
        WORKING_SPACE_REDUNDANTLY(183),
        WRITABLE(184),
        ENTER_JAVADOC_COMMENT(185),
        ENTER_MULTILINE_COMMENT(186),
        JAVADOC_COMMENT(187),
        MULTI_LINE_COMMENT(188),
        COMMENT_CONTENT(189),
        ABSTRACT(190),
        ASSERT(191),
        BOOLEAN(192),
        BREAK(193),
        BYTE(194),
        CASE(195),
        CATCH(196),
        CHAR(197),
        CLASS(198),
        CONST(199),
        CONTINUE(200),
        _DEFAULT(201),
        DO(202),
        DOUBLE(203),
        ELSE(204),
        ENUM(205),
        EXTENDS(206),
        FALSE(207),
        FINAL(208),
        FINALLY(209),
        FLOAT(210),
        FOR(211),
        GOTO(212),
        IF(213),
        IMPLEMENTS(214),
        IMPORT(215),
        INSTANCEOF(216),
        INT(217),
        INTERFACE(218),
        LONG(219),
        NATIVE(220),
        NEW(221),
        NULL(222),
        PACKAGE(223),
        PRIVATE(224),
        PROTECTED(225),
        PUBLIC(226),
        RECORD(227),
        RETURN(228),
        SHORT(229),
        STATIC(230),
        STRICTFP(231),
        SUPER(232),
        SWITCH(233),
        SYNCHRONIZED(234),
        THIS(235),
        THROW(236),
        THROWS(237),
        TRANSIENT(238),
        TRUE(239),
        TRY(240),
        VOID(241),
        VOLATILE(242),
        WHILE(243),
        YIELD(244),
        REQUIRES(245),
        TO(246),
        WITH(247),
        OPEN(248),
        OPENS(249),
        USES(250),
        MODULE(251),
        EXPORTS(252),
        PROVIDES(253),
        TRANSITIVE(254),
        LONG_LITERAL(255),
        INTEGER_LITERAL(256),
        DECIMAL_LITERAL(257),
        HEX_LITERAL(258),
        OCTAL_LITERAL(259),
        BINARY_LITERAL(260),
        FLOATING_POINT_LITERAL(261),
        DECIMAL_FLOATING_POINT_LITERAL(262),
        DECIMAL_EXPONENT(263),
        HEXADECIMAL_FLOATING_POINT_LITERAL(264),
        HEXADECIMAL_EXPONENT(265),
        HEX_DIGITS(266),
        UNICODE_ESCAPE(267),
        CHARACTER_LITERAL(268),
        STRING_LITERAL(269),
        ENTER_TEXT_BLOCK(270),
        TEXT_BLOCK_LITERAL(271),
        TEXT_BLOCK_CONTENT(272),
        JML_IDENTIFIER(273),
        IDENTIFIER(274),
        LETTER(275),
        PART_LETTER(276),
        LPAREN(277),
        RPAREN(278),
        LBRACE(279),
        RBRACE(280),
        LBRACKET(281),
        RBRACKET(282),
        SEMICOLON(283),
        COMMA(284),
        DOT(285),
        ELLIPSIS(286),
        AT(287),
        DOUBLECOLON(288),
        ASSIGN(289),
        LT(290),
        BANG(291),
        TILDE(292),
        HOOK(293),
        COLON(294),
        ARROW(295),
        EQ(296),
        GE(297),
        LE(298),
        NE(299),
        SC_AND(300),
        SC_OR(301),
        INCR(302),
        DECR(303),
        PLUS(304),
        MINUS(305),
        STAR(306),
        SLASH(307),
        BIT_AND(308),
        BIT_OR(309),
        XOR(310),
        REM(311),
        LSHIFT(312),
        PLUSASSIGN(313),
        MINUSASSIGN(314),
        STARASSIGN(315),
        SLASHASSIGN(316),
        ANDASSIGN(317),
        ORASSIGN(318),
        XORASSIGN(319),
        REMASSIGN(320),
        LSHIFTASSIGN(321),
        RSIGNEDSHIFTASSIGN(322),
        RUNSIGNEDSHIFTASSIGN(323),
        RUNSIGNEDSHIFT(324),
        RSIGNEDSHIFT(325),
        GT(326),
        CTRL_Z(327);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 327:
                    return CTRL_Z;
                case 326:
                    return GT;
                case 325:
                    return RSIGNEDSHIFT;
                case 324:
                    return RUNSIGNEDSHIFT;
                case 323:
                    return RUNSIGNEDSHIFTASSIGN;
                case 322:
                    return RSIGNEDSHIFTASSIGN;
                case 321:
                    return LSHIFTASSIGN;
                case 320:
                    return REMASSIGN;
                case 319:
                    return XORASSIGN;
                case 318:
                    return ORASSIGN;
                case 317:
                    return ANDASSIGN;
                case 316:
                    return SLASHASSIGN;
                case 315:
                    return STARASSIGN;
                case 314:
                    return MINUSASSIGN;
                case 313:
                    return PLUSASSIGN;
                case 312:
                    return LSHIFT;
                case 311:
                    return REM;
                case 310:
                    return XOR;
                case 309:
                    return BIT_OR;
                case 308:
                    return BIT_AND;
                case 307:
                    return SLASH;
                case 306:
                    return STAR;
                case 305:
                    return MINUS;
                case 304:
                    return PLUS;
                case 303:
                    return DECR;
                case 302:
                    return INCR;
                case 301:
                    return SC_OR;
                case 300:
                    return SC_AND;
                case 299:
                    return NE;
                case 298:
                    return LE;
                case 297:
                    return GE;
                case 296:
                    return EQ;
                case 295:
                    return ARROW;
                case 294:
                    return COLON;
                case 293:
                    return HOOK;
                case 292:
                    return TILDE;
                case 291:
                    return BANG;
                case 290:
                    return LT;
                case 289:
                    return ASSIGN;
                case 288:
                    return DOUBLECOLON;
                case 287:
                    return AT;
                case 286:
                    return ELLIPSIS;
                case 285:
                    return DOT;
                case 284:
                    return COMMA;
                case 283:
                    return SEMICOLON;
                case 282:
                    return RBRACKET;
                case 281:
                    return LBRACKET;
                case 280:
                    return RBRACE;
                case 279:
                    return LBRACE;
                case 278:
                    return RPAREN;
                case 277:
                    return LPAREN;
                case 276:
                    return PART_LETTER;
                case 275:
                    return LETTER;
                case 274:
                    return IDENTIFIER;
                case 273:
                    return JML_IDENTIFIER;
                case 272:
                    return TEXT_BLOCK_CONTENT;
                case 271:
                    return TEXT_BLOCK_LITERAL;
                case 270:
                    return ENTER_TEXT_BLOCK;
                case 269:
                    return STRING_LITERAL;
                case 268:
                    return CHARACTER_LITERAL;
                case 267:
                    return UNICODE_ESCAPE;
                case 266:
                    return HEX_DIGITS;
                case 265:
                    return HEXADECIMAL_EXPONENT;
                case 264:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 263:
                    return DECIMAL_EXPONENT;
                case 262:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 261:
                    return FLOATING_POINT_LITERAL;
                case 260:
                    return BINARY_LITERAL;
                case 259:
                    return OCTAL_LITERAL;
                case 258:
                    return HEX_LITERAL;
                case 257:
                    return DECIMAL_LITERAL;
                case 256:
                    return INTEGER_LITERAL;
                case 255:
                    return LONG_LITERAL;
                case 254:
                    return TRANSITIVE;
                case 253:
                    return PROVIDES;
                case 252:
                    return EXPORTS;
                case 251:
                    return MODULE;
                case 250:
                    return USES;
                case 249:
                    return OPENS;
                case 248:
                    return OPEN;
                case 247:
                    return WITH;
                case 246:
                    return TO;
                case 245:
                    return REQUIRES;
                case 244:
                    return YIELD;
                case 243:
                    return WHILE;
                case 242:
                    return VOLATILE;
                case 241:
                    return VOID;
                case 240:
                    return TRY;
                case 239:
                    return TRUE;
                case 238:
                    return TRANSIENT;
                case 237:
                    return THROWS;
                case 236:
                    return THROW;
                case 235:
                    return THIS;
                case 234:
                    return SYNCHRONIZED;
                case 233:
                    return SWITCH;
                case 232:
                    return SUPER;
                case 231:
                    return STRICTFP;
                case 230:
                    return STATIC;
                case 229:
                    return SHORT;
                case 228:
                    return RETURN;
                case 227:
                    return RECORD;
                case 226:
                    return PUBLIC;
                case 225:
                    return PROTECTED;
                case 224:
                    return PRIVATE;
                case 223:
                    return PACKAGE;
                case 222:
                    return NULL;
                case 221:
                    return NEW;
                case 220:
                    return NATIVE;
                case 219:
                    return LONG;
                case 218:
                    return INTERFACE;
                case 217:
                    return INT;
                case 216:
                    return INSTANCEOF;
                case 215:
                    return IMPORT;
                case 214:
                    return IMPLEMENTS;
                case 213:
                    return IF;
                case 212:
                    return GOTO;
                case 211:
                    return FOR;
                case 210:
                    return FLOAT;
                case 209:
                    return FINALLY;
                case 208:
                    return FINAL;
                case 207:
                    return FALSE;
                case 206:
                    return EXTENDS;
                case 205:
                    return ENUM;
                case 204:
                    return ELSE;
                case 203:
                    return DOUBLE;
                case 202:
                    return DO;
                case 201:
                    return _DEFAULT;
                case 200:
                    return CONTINUE;
                case 199:
                    return CONST;
                case 198:
                    return CLASS;
                case 197:
                    return CHAR;
                case 196:
                    return CATCH;
                case 195:
                    return CASE;
                case 194:
                    return BYTE;
                case 193:
                    return BREAK;
                case 192:
                    return BOOLEAN;
                case 191:
                    return ASSERT;
                case 190:
                    return ABSTRACT;
                case 189:
                    return COMMENT_CONTENT;
                case 188:
                    return MULTI_LINE_COMMENT;
                case 187:
                    return JAVADOC_COMMENT;
                case 186:
                    return ENTER_MULTILINE_COMMENT;
                case 185:
                    return ENTER_JAVADOC_COMMENT;
                case 184:
                    return WRITABLE;
                case 183:
                    return WORKING_SPACE_REDUNDANTLY;
                case 182:
                    return WORKING_SPACE;
                case 181:
                    return WORKING_SPACE_ESC;
                case 180:
                    return WHEN_REDUNDANTLY;
                case 179:
                    return WHEN;
                case 178:
                    return WARN_OP;
                case 177:
                    return WARN;
                case 176:
                    return UNREACHABLE;
                case 175:
                    return UNKNOWN_OP_EQ;
                case 174:
                    return UNKNOWN_OP;
                case 173:
                    return UNINITIALIZED;
                case 172:
                    return TYPEOF;
                case 171:
                    return TYPE;
                case 170:
                    return SUM;
                case 169:
                    return SUCH_THAT;
                case 168:
                    return SUBTYPE;
                case 167:
                    return STRICTLY_PURE;
                case 166:
                    return STATIC_INITIALIZER;
                case 165:
                    return SPEC_SAFE_MATH;
                case 164:
                    return SPEC_PUBLIC;
                case 163:
                    return SPEC_PROTECTED;
                case 162:
                    return SPEC_PRIVATE;
                case 161:
                    return SPEC_PACKAGE;
                case 160:
                    return SPEC_JAVA_MATH;
                case 159:
                    return SPEC_BIGINT_MATH;
                case 158:
                    return SIGNALS_REDUNDANTLY;
                case 157:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 156:
                    return SIGNALS_ONLY;
                case 155:
                    return SIGNALS;
                case 154:
                    return SET;
                case 153:
                    return SAFE_MATH;
                case 152:
                    return RETURN_BEHAVIOUR;
                case 151:
                    return RETURN_BEHAVIOR;
                case 150:
                    return RETURNS_REDUNDANTLY;
                case 149:
                    return RETURNS;
                case 148:
                    return RESULT;
                case 147:
                    return REQUIRES_REDUNDANTLY;
                case 146:
                    return REPRESENTS_REDUNDANTLY;
                case 145:
                    return REPRESENTS;
                case 144:
                    return REFINING;
                case 143:
                    return REAL;
                case 142:
                    return READABLE;
                case 141:
                    return REACH;
                case 140:
                    return PURE;
                case 139:
                    return PRODUCT;
                case 138:
                    return PRE_REDUNDANTLY;
                case 137:
                    return PRE;
                case 136:
                    return PRE_ESC;
                case 135:
                    return POST_REDUNDANTLY;
                case 134:
                    return POST;
                case 133:
                    return OR;
                case 132:
                    return OLD;
                case 131:
                    return NUM_OF;
                case 130:
                    return NULLABLE_BY_DEFAULT;
                case 129:
                    return NULLABLE;
                case 128:
                    return NOWARN_OP;
                case 127:
                    return NOWARN;
                case 126:
                    return NORMAL_EXAMPLE;
                case 125:
                    return NORMAL_BEHAVIOUR;
                case 124:
                    return NORMAL_BEHAVIOR;
                case 123:
                    return NON_NULL;
                case 122:
                    return NONNULLELEMENTS;
                case 121:
                    return NEW_OBJECT;
                case 120:
                    return NESTED_CONTRACT_START;
                case 119:
                    return NESTED_CONTRACT_END;
                case 118:
                    return MONITORS_FOR;
                case 117:
                    return MONITORED;
                case 116:
                    return MODIFIES_REDUNDANTLY;
                case 115:
                    return MODIFIES;
                case 114:
                    return MODIFIABLE_REDUNDANTLY;
                case 113:
                    return MODIFIABLE;
                case 112:
                    return MODEL_PROGRAM;
                case 111:
                    return MODEL;
                case 110:
                    return MIN;
                case 109:
                    return METHOD;
                case 108:
                    return MEASURED_BY_REDUNDANTLY;
                case 107:
                    return ESC_MEASURED_BY;
                case 106:
                    return MEASURED_BY;
                case 105:
                    return MAX;
                case 104:
                    return MAPS_REDUNDANTLY;
                case 103:
                    return MAPS;
                case 102:
                    return MAINTAINING_REDUNDANTLY;
                case 101:
                    return MAINTAINING;
                case 100:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 99:
                    return LOOP_INVARIANT;
                case 98:
                    return JAVA_MATH;
                case 97:
                    return IN_REDUNDANTLY;
                case 96:
                    return INVARIANT_REDUNDANTLY;
                case 95:
                    return NO_STATE;
                case 94:
                    return TWO_STATE;
                case 93:
                    return INSTANCE;
                case 92:
                    return INITIALLY;
                case 91:
                    return INITIALIZER;
                case 90:
                    return IN;
                case 89:
                    return IMPLIES_THAT;
                case 88:
                    return HENCE_BY_REDUNDANTLY;
                case 87:
                    return HENCE_BY;
                case 86:
                    return HELPER;
                case 85:
                    return GHOST;
                case 84:
                    return FOR_EXAMPLE;
                case 83:
                    return FORALL;
                case 82:
                    return FORALLQ;
                case 81:
                    return FIELD;
                case 80:
                    return EXTRACT;
                case 79:
                    return EXSURES_REDUNDANTLY;
                case 78:
                    return EXSURES;
                case 77:
                    return EXISTS;
                case 76:
                    return EXCEPTIONAL_EXAMPLE;
                case 75:
                    return EXCEPTIONAL_BEHAVIOUR;
                case 74:
                    return EXCEPTIONAL_BEHAVIOR;
                case 73:
                    return EXAMPLE;
                case 72:
                    return ERASES;
                case 71:
                    return IMPLICATION_BACKWARD;
                case 70:
                    return IMPLICATION;
                case 69:
                    return EQUIVALENCE;
                case 68:
                    return REQUIRES_FREE;
                case 67:
                    return ENSURES_FREE;
                case 66:
                    return ENSURES_REDUNDANTLY;
                case 65:
                    return ENSURES;
                case 64:
                    return ELEMTYPE;
                case 63:
                    return DURATION_REDUNDANTLY;
                case 62:
                    return DURATION;
                case 61:
                    return DIVERGES_REDUNDANTLY;
                case 60:
                    return DIVERGES;
                case 59:
                    return DETERMINES;
                case 58:
                    return DECREASING_REDUNDANTLY;
                case 57:
                    return DECREASING;
                case 56:
                    return DECREASES_REDUNDANTLY;
                case 55:
                    return DECREASES;
                case 54:
                    return DECLASSIFIES;
                case 53:
                    return CONTINUE_BEHAVIOUR;
                case 52:
                    return CONTINUE_BEHAVIOR;
                case 51:
                    return CONTINUES_REDUNDANTLY;
                case 50:
                    return CONTINUES;
                case 49:
                    return CONSTRUCTOR;
                case 48:
                    return CONSTRAINT_REDUNDANTLY;
                case 47:
                    return CONSTRAINT;
                case 46:
                    return CODE_SAFE_MATH;
                case 45:
                    return CODE_JAVA_MATH;
                case 44:
                    return CODE_BIGINT_MATH;
                case 43:
                    return CODE;
                case 42:
                    return CHOOSE_IF;
                case 41:
                    return CHOOSE;
                case 40:
                    return CAPTURES_REDUNDANTLY;
                case 39:
                    return CAPTURES;
                case 38:
                    return CALLABLE_REDUNDANTLY;
                case 37:
                    return CALLABLE;
                case 36:
                    return BREAK_BEHAVIOUR;
                case 35:
                    return BREAK_BEHAVIOR;
                case 34:
                    return BREAKS_REDUNDANTLY;
                case 33:
                    return BREAKS;
                case 32:
                    return BIGINT_MATH;
                case 31:
                    return BIGINT;
                case 30:
                    return BEHAVIOUR;
                case 29:
                    return BEHAVIOR;
                case 28:
                    return AXIOM;
                case 27:
                    return ASSUME_REDUNDANTLY;
                case 26:
                    return ASSUME;
                case 25:
                    return ASSIGNABLE_REDUNDANTLY;
                case 24:
                    return ASSIGNABLE;
                case 23:
                    return ASSERT_REDUNDANTLY;
                case 22:
                    return ANTIVALENCE;
                case 21:
                    return ALSO;
                case 20:
                    return ACCESSIBLE_REDUNDANTLY;
                case 19:
                    return ACCESSIBLE;
                case 18:
                    return MODEL_BEHAVIOUR;
                case 17:
                    return MODEL_BEHAVIOR;
                case 16:
                    return ABRUPT_BEHAVIOUR;
                case 15:
                    return ABRUPT_BEHAVIOR;
                case 14:
                    return INVARIANT;
                case 13:
                    return JML_SINGLE_END;
                case 12:
                    return JML_MULTI_END;
                case 11:
                    return JML_MULTI_START;
                case 10:
                    return JML_SINGLE_START;
                case 9:
                    return SINGLE_LINE_COMMENT;
                case 8:
                    return SINGLE_LINE_COMMENT0;
                case 7:
                    return JML_SINGLE_START0;
                case 6:
                    return SINGLE_LINE_COMMENT_IN_MULTI_JML;
                case 5:
                    return OLD_MAC_EOL;
                case 4:
                    return UNIX_EOL;
                case 3:
                    return WINDOWS_EOL;
                case 2:
                    return SPACE;
                case 1:
                    return AT_AT_BEGINN;
                case 0:
                    return EOF;
                default:
                    throw new IllegalArgumentException(f("Token kind %d is unknown.", kind));
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
