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
        String text = getText()
                .replace("\n", "\\n")
                .replace("\r", "\\r")
                .replace("\r\n", "\\r\\n")
                .replace("\t", "\\t");
        return f(
                "\"%s\"   <%s>   %s",
                text, getKind(), getRange().map(Range::toString).orElse("(?)-(?)"));
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
        INVARIANT(5),
        ABRUPT_BEHAVIOR(6),
        ABRUPT_BEHAVIOUR(7),
        MODEL_BEHAVIOR(8),
        MODEL_BEHAVIOUR(9),
        ACCESSIBLE(10),
        ACCESSIBLE_REDUNDANTLY(11),
        ALSO(12),
        ANTIVALENCE(13),
        ASSERT_REDUNDANTLY(14),
        ASSIGNABLE(15),
        ASSIGNABLE_REDUNDANTLY(16),
        ASSUME(17),
        ASSUME_REDUNDANTLY(18),
        AXIOM(19),
        BEHAVIOR(20),
        BEHAVIOUR(21),
        BIGINT(22),
        BIGINT_MATH(23),
        BREAKS(24),
        BREAKS_REDUNDANTLY(25),
        BREAK_BEHAVIOR(26),
        BREAK_BEHAVIOUR(27),
        CALLABLE(28),
        CALLABLE_REDUNDANTLY(29),
        CAPTURES(30),
        CAPTURES_REDUNDANTLY(31),
        CHOOSE(32),
        CHOOSE_IF(33),
        CODE(34),
        CODE_BIGINT_MATH(35),
        CODE_JAVA_MATH(36),
        CODE_SAFE_MATH(37),
        IMMUTABLE(38),
        CONSTRAINT(39),
        CONSTRAINT_REDUNDANTLY(40),
        CONSTRUCTOR(41),
        CONTINUES(42),
        CONTINUES_REDUNDANTLY(43),
        CONTINUE_BEHAVIOR(44),
        CONTINUE_BEHAVIOUR(45),
        DECLASSIFIES(46),
        DECREASES(47),
        DECREASES_REDUNDANTLY(48),
        DECREASING(49),
        DECREASING_REDUNDANTLY(50),
        DETERMINES(51),
        DIVERGES(52),
        DIVERGES_REDUNDANTLY(53),
        DURATION(54),
        DURATION_REDUNDANTLY(55),
        ENSURES(56),
        ENSURES_REDUNDANTLY(57),
        ENSURES_FREE(58),
        REQUIRES_FREE(59),
        EQUIVALENCE(60),
        IMPLICATION(61),
        IMPLICATION_BACKWARD(62),
        ERASES(63),
        EXAMPLE(64),
        EXCEPTIONAL_BEHAVIOR(65),
        EXCEPTIONAL_BEHAVIOUR(66),
        EXCEPTIONAL_EXAMPLE(67),
        EXISTS(68),
        EXSURES(69),
        EXSURES_REDUNDANTLY(70),
        EXTRACT(71),
        FIELD(72),
        FORALLQ(73),
        LET(74),
        FORALL(75),
        FOR_EXAMPLE(76),
        PEER(77),
        REP(78),
        READ_ONLY(79),
        GHOST(80),
        BEGIN(81),
        END(82),
        HELPER(83),
        HENCE_BY(84),
        HENCE_BY_REDUNDANTLY(85),
        IMPLIES_THAT(86),
        IN(87),
        INITIALIZER(88),
        INITIALLY(89),
        INSTANCE(90),
        TWO_STATE(91),
        NO_STATE(92),
        NON_NULL_BY_DEFAULT(93),
        INVARIANT_REDUNDANTLY(94),
        IN_REDUNDANTLY(95),
        JAVA_MATH(96),
        LBLNEG(97),
        LBLPOS(98),
        LBL(99),
        LOOP_CONTRACT(100),
        LOOP_INVARIANT(101),
        LOOP_INVARIANT_FREE(102),
        LOOP_INVARIANT_REDUNDANTLY(103),
        MAINTAINING(104),
        MAINTAINING_REDUNDANTLY(105),
        MAPS(106),
        MAPS_REDUNDANTLY(107),
        MAX(108),
        MEASURED_BY(109),
        ESC_MEASURED_BY(110),
        MEASURED_BY_REDUNDANTLY(111),
        METHOD(112),
        MIN(113),
        MODEL(114),
        MODEL_PROGRAM(115),
        MODIFIABLE(116),
        MODIFIABLE_REDUNDANTLY(117),
        LOOP_MODIFIES(118),
        MODIFIES(119),
        MODIFIES_REDUNDANTLY(120),
        MONITORED(121),
        MONITORS_FOR(122),
        NESTED_CONTRACT_END(123),
        NESTED_CONTRACT_START(124),
        NEW_OBJECT(125),
        NONNULLELEMENTS(126),
        NON_NULL(127),
        NORMAL_BEHAVIOR(128),
        NORMAL_BEHAVIOUR(129),
        FEASIBLE_BEHAVIOR(130),
        FEASIBLE_BEHAVIOUR(131),
        NORMAL_EXAMPLE(132),
        NOWARN(133),
        NOWARN_OP(134),
        NULLABLE(135),
        NULLABLE_BY_DEFAULT(136),
        NUM_OF(137),
        OLD(138),
        OR(139),
        POST(140),
        POST_REDUNDANTLY(141),
        PRE_ESC(142),
        PRE(143),
        PRE_REDUNDANTLY(144),
        PRODUCT(145),
        PURE(146),
        READABLE(147),
        REFINING(148),
        REPRESENTS(149),
        REPRESENTS_REDUNDANTLY(150),
        REQUIRES_REDUNDANTLY(151),
        RESULT(152),
        RETURNS(153),
        RETURNS_REDUNDANTLY(154),
        RETURN_BEHAVIOR(155),
        BACKARROW(156),
        RETURN_BEHAVIOUR(157),
        SAFE_MATH(158),
        SET(159),
        SIGNALS(160),
        SIGNALS_ONLY(161),
        SIGNALS_ONLY_REDUNDANTLY(162),
        SIGNALS_REDUNDANTLY(163),
        SPEC_BIGINT_MATH(164),
        SPEC_JAVA_MATH(165),
        SPEC_PACKAGE(166),
        SPEC_PRIVATE(167),
        SPEC_PROTECTED(168),
        SPEC_PUBLIC(169),
        SPEC_SAFE_MATH(170),
        STATIC_INITIALIZER(171),
        STRICTLY_PURE(172),
        SUBTYPE(173),
        SUCH_THAT(174),
        SUM(175),
        TYPE(176),
        UNINITIALIZED(177),
        UNKNOWN_OP(178),
        UNKNOWN_OP_EQ(179),
        UNREACHABLE(180),
        WARN(181),
        WARN_OP(182),
        WHEN_REDUNDANTLY(183),
        WORKING_SPACE_ESC(184),
        WORKING_SPACE(185),
        WORKING_SPACE_REDUNDANTLY(186),
        WRITABLE(187),
        DOTDOT(188),
        JML_LINE_COMMENT(189),
        SINGLE_LINE_COMMENT(190),
        JML_ENTER_MULTILINE_COMMENT(191),
        ENTER_JAVADOC_COMMENT(192),
        ENTER_JML_BLOCK_COMMENT(193),
        ENTER_MULTILINE_COMMENT(194),
        JML_BLOCK_COMMENT(195),
        JAVADOC_COMMENT(196),
        MULTI_LINE_COMMENT(197),
        JML_MULTI_LINE_COMMENT(198),
        COMMENT_CONTENT(199),
        ABSTRACT(200),
        ASSERT(201),
        BOOLEAN(202),
        BREAK(203),
        BYTE(204),
        CASE(205),
        CATCH(206),
        CHAR(207),
        CLASS(208),
        CONST(209),
        CONTINUE(210),
        _DEFAULT(211),
        DO(212),
        DOUBLE(213),
        ELSE(214),
        ENUM(215),
        EXTENDS(216),
        FALSE(217),
        FINAL(218),
        FINALLY(219),
        FLOAT(220),
        FOR(221),
        GOTO(222),
        IF(223),
        IMPLEMENTS(224),
        IMPORT(225),
        INSTANCEOF(226),
        INT(227),
        INTERFACE(228),
        LONG(229),
        NATIVE(230),
        NEW(231),
        NON_SEALED(232),
        NULL(233),
        PACKAGE(234),
        PERMITS(235),
        PRIVATE(236),
        PROTECTED(237),
        PUBLIC(238),
        RECORD(239),
        RETURN(240),
        SEALED(241),
        SHORT(242),
        STATIC(243),
        STRICTFP(244),
        SUPER(245),
        SWITCH(246),
        SYNCHRONIZED(247),
        THIS(248),
        THROW(249),
        THROWS(250),
        TRANSIENT(251),
        TRUE(252),
        TRY(253),
        VOID(254),
        VOLATILE(255),
        WHILE(256),
        YIELD(257),
        REQUIRES(258),
        TO(259),
        WITH(260),
        OPEN(261),
        OPENS(262),
        USES(263),
        MODULE(264),
        EXPORTS(265),
        PROVIDES(266),
        TRANSITIVE(267),
        WHEN(268),
        LONG_LITERAL(269),
        INTEGER_LITERAL(270),
        DECIMAL_LITERAL(271),
        HEX_LITERAL(272),
        OCTAL_LITERAL(273),
        BINARY_LITERAL(274),
        FLOATING_POINT_LITERAL(275),
        DECIMAL_FLOATING_POINT_LITERAL(276),
        DECIMAL_EXPONENT(277),
        HEXADECIMAL_FLOATING_POINT_LITERAL(278),
        HEXADECIMAL_EXPONENT(279),
        HEX_DIGITS(280),
        UNICODE_ESCAPE(281),
        CHARACTER_LITERAL(282),
        STRING_LITERAL(283),
        ENTER_TEXT_BLOCK(284),
        TEXT_BLOCK_LITERAL(285),
        TEXT_BLOCK_CONTENT(286),
        JML_IDENTIFIER(287),
        IDENTIFIER(288),
        SYNTH_IDENTIFIER(289),
        LETTER(290),
        PART_LETTER(291),
        LPAREN(292),
        RPAREN(293),
        LBRACE(294),
        RBRACE(295),
        LBRACKET(296),
        RBRACKET(297),
        SEMICOLON(298),
        COMMA(299),
        DOT(300),
        ELLIPSIS(301),
        AT(302),
        DOUBLECOLON(303),
        ASSIGN(304),
        LT(305),
        BANG(306),
        TILDE(307),
        HOOK(308),
        COLON(309),
        ARROW(310),
        EQ(311),
        GE(312),
        LE(313),
        NE(314),
        SC_AND(315),
        SC_OR(316),
        INCR(317),
        DECR(318),
        PLUS(319),
        MINUS(320),
        STAR(321),
        SLASH(322),
        BIT_AND(323),
        BIT_OR(324),
        XOR(325),
        REM(326),
        LSHIFT(327),
        PLUSASSIGN(328),
        MINUSASSIGN(329),
        STARASSIGN(330),
        SLASHASSIGN(331),
        ANDASSIGN(332),
        ORASSIGN(333),
        XORASSIGN(334),
        REMASSIGN(335),
        LSHIFTASSIGN(336),
        RSIGNEDSHIFTASSIGN(337),
        RUNSIGNEDSHIFTASSIGN(338),
        RUNSIGNEDSHIFT(339),
        RSIGNEDSHIFT(340),
        GT(341),
        CTRL_Z(342);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 342:
                    return CTRL_Z;
                case 341:
                    return GT;
                case 340:
                    return RSIGNEDSHIFT;
                case 339:
                    return RUNSIGNEDSHIFT;
                case 338:
                    return RUNSIGNEDSHIFTASSIGN;
                case 337:
                    return RSIGNEDSHIFTASSIGN;
                case 336:
                    return LSHIFTASSIGN;
                case 335:
                    return REMASSIGN;
                case 334:
                    return XORASSIGN;
                case 333:
                    return ORASSIGN;
                case 332:
                    return ANDASSIGN;
                case 331:
                    return SLASHASSIGN;
                case 330:
                    return STARASSIGN;
                case 329:
                    return MINUSASSIGN;
                case 328:
                    return PLUSASSIGN;
                case 327:
                    return LSHIFT;
                case 326:
                    return REM;
                case 325:
                    return XOR;
                case 324:
                    return BIT_OR;
                case 323:
                    return BIT_AND;
                case 322:
                    return SLASH;
                case 321:
                    return STAR;
                case 320:
                    return MINUS;
                case 319:
                    return PLUS;
                case 318:
                    return DECR;
                case 317:
                    return INCR;
                case 316:
                    return SC_OR;
                case 315:
                    return SC_AND;
                case 314:
                    return NE;
                case 313:
                    return LE;
                case 312:
                    return GE;
                case 311:
                    return EQ;
                case 310:
                    return ARROW;
                case 309:
                    return COLON;
                case 308:
                    return HOOK;
                case 307:
                    return TILDE;
                case 306:
                    return BANG;
                case 305:
                    return LT;
                case 304:
                    return ASSIGN;
                case 303:
                    return DOUBLECOLON;
                case 302:
                    return AT;
                case 301:
                    return ELLIPSIS;
                case 300:
                    return DOT;
                case 299:
                    return COMMA;
                case 298:
                    return SEMICOLON;
                case 297:
                    return RBRACKET;
                case 296:
                    return LBRACKET;
                case 295:
                    return RBRACE;
                case 294:
                    return LBRACE;
                case 293:
                    return RPAREN;
                case 292:
                    return LPAREN;
                case 291:
                    return PART_LETTER;
                case 290:
                    return LETTER;
                case 289:
                    return SYNTH_IDENTIFIER;
                case 288:
                    return IDENTIFIER;
                case 287:
                    return JML_IDENTIFIER;
                case 286:
                    return TEXT_BLOCK_CONTENT;
                case 285:
                    return TEXT_BLOCK_LITERAL;
                case 284:
                    return ENTER_TEXT_BLOCK;
                case 283:
                    return STRING_LITERAL;
                case 282:
                    return CHARACTER_LITERAL;
                case 281:
                    return UNICODE_ESCAPE;
                case 280:
                    return HEX_DIGITS;
                case 279:
                    return HEXADECIMAL_EXPONENT;
                case 278:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 277:
                    return DECIMAL_EXPONENT;
                case 276:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 275:
                    return FLOATING_POINT_LITERAL;
                case 274:
                    return BINARY_LITERAL;
                case 273:
                    return OCTAL_LITERAL;
                case 272:
                    return HEX_LITERAL;
                case 271:
                    return DECIMAL_LITERAL;
                case 270:
                    return INTEGER_LITERAL;
                case 269:
                    return LONG_LITERAL;
                case 268:
                    return WHEN;
                case 267:
                    return TRANSITIVE;
                case 266:
                    return PROVIDES;
                case 265:
                    return EXPORTS;
                case 264:
                    return MODULE;
                case 263:
                    return USES;
                case 262:
                    return OPENS;
                case 261:
                    return OPEN;
                case 260:
                    return WITH;
                case 259:
                    return TO;
                case 258:
                    return REQUIRES;
                case 257:
                    return YIELD;
                case 256:
                    return WHILE;
                case 255:
                    return VOLATILE;
                case 254:
                    return VOID;
                case 253:
                    return TRY;
                case 252:
                    return TRUE;
                case 251:
                    return TRANSIENT;
                case 250:
                    return THROWS;
                case 249:
                    return THROW;
                case 248:
                    return THIS;
                case 247:
                    return SYNCHRONIZED;
                case 246:
                    return SWITCH;
                case 245:
                    return SUPER;
                case 244:
                    return STRICTFP;
                case 243:
                    return STATIC;
                case 242:
                    return SHORT;
                case 241:
                    return SEALED;
                case 240:
                    return RETURN;
                case 239:
                    return RECORD;
                case 238:
                    return PUBLIC;
                case 237:
                    return PROTECTED;
                case 236:
                    return PRIVATE;
                case 235:
                    return PERMITS;
                case 234:
                    return PACKAGE;
                case 233:
                    return NULL;
                case 232:
                    return NON_SEALED;
                case 231:
                    return NEW;
                case 230:
                    return NATIVE;
                case 229:
                    return LONG;
                case 228:
                    return INTERFACE;
                case 227:
                    return INT;
                case 226:
                    return INSTANCEOF;
                case 225:
                    return IMPORT;
                case 224:
                    return IMPLEMENTS;
                case 223:
                    return IF;
                case 222:
                    return GOTO;
                case 221:
                    return FOR;
                case 220:
                    return FLOAT;
                case 219:
                    return FINALLY;
                case 218:
                    return FINAL;
                case 217:
                    return FALSE;
                case 216:
                    return EXTENDS;
                case 215:
                    return ENUM;
                case 214:
                    return ELSE;
                case 213:
                    return DOUBLE;
                case 212:
                    return DO;
                case 211:
                    return _DEFAULT;
                case 210:
                    return CONTINUE;
                case 209:
                    return CONST;
                case 208:
                    return CLASS;
                case 207:
                    return CHAR;
                case 206:
                    return CATCH;
                case 205:
                    return CASE;
                case 204:
                    return BYTE;
                case 203:
                    return BREAK;
                case 202:
                    return BOOLEAN;
                case 201:
                    return ASSERT;
                case 200:
                    return ABSTRACT;
                case 199:
                    return COMMENT_CONTENT;
                case 198:
                    return JML_MULTI_LINE_COMMENT;
                case 197:
                    return MULTI_LINE_COMMENT;
                case 196:
                    return JAVADOC_COMMENT;
                case 195:
                    return JML_BLOCK_COMMENT;
                case 194:
                    return ENTER_MULTILINE_COMMENT;
                case 193:
                    return ENTER_JML_BLOCK_COMMENT;
                case 192:
                    return ENTER_JAVADOC_COMMENT;
                case 191:
                    return JML_ENTER_MULTILINE_COMMENT;
                case 190:
                    return SINGLE_LINE_COMMENT;
                case 189:
                    return JML_LINE_COMMENT;
                case 188:
                    return DOTDOT;
                case 187:
                    return WRITABLE;
                case 186:
                    return WORKING_SPACE_REDUNDANTLY;
                case 185:
                    return WORKING_SPACE;
                case 184:
                    return WORKING_SPACE_ESC;
                case 183:
                    return WHEN_REDUNDANTLY;
                case 182:
                    return WARN_OP;
                case 181:
                    return WARN;
                case 180:
                    return UNREACHABLE;
                case 179:
                    return UNKNOWN_OP_EQ;
                case 178:
                    return UNKNOWN_OP;
                case 177:
                    return UNINITIALIZED;
                case 176:
                    return TYPE;
                case 175:
                    return SUM;
                case 174:
                    return SUCH_THAT;
                case 173:
                    return SUBTYPE;
                case 172:
                    return STRICTLY_PURE;
                case 171:
                    return STATIC_INITIALIZER;
                case 170:
                    return SPEC_SAFE_MATH;
                case 169:
                    return SPEC_PUBLIC;
                case 168:
                    return SPEC_PROTECTED;
                case 167:
                    return SPEC_PRIVATE;
                case 166:
                    return SPEC_PACKAGE;
                case 165:
                    return SPEC_JAVA_MATH;
                case 164:
                    return SPEC_BIGINT_MATH;
                case 163:
                    return SIGNALS_REDUNDANTLY;
                case 162:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 161:
                    return SIGNALS_ONLY;
                case 160:
                    return SIGNALS;
                case 159:
                    return SET;
                case 158:
                    return SAFE_MATH;
                case 157:
                    return RETURN_BEHAVIOUR;
                case 156:
                    return BACKARROW;
                case 155:
                    return RETURN_BEHAVIOR;
                case 154:
                    return RETURNS_REDUNDANTLY;
                case 153:
                    return RETURNS;
                case 152:
                    return RESULT;
                case 151:
                    return REQUIRES_REDUNDANTLY;
                case 150:
                    return REPRESENTS_REDUNDANTLY;
                case 149:
                    return REPRESENTS;
                case 148:
                    return REFINING;
                case 147:
                    return READABLE;
                case 146:
                    return PURE;
                case 145:
                    return PRODUCT;
                case 144:
                    return PRE_REDUNDANTLY;
                case 143:
                    return PRE;
                case 142:
                    return PRE_ESC;
                case 141:
                    return POST_REDUNDANTLY;
                case 140:
                    return POST;
                case 139:
                    return OR;
                case 138:
                    return OLD;
                case 137:
                    return NUM_OF;
                case 136:
                    return NULLABLE_BY_DEFAULT;
                case 135:
                    return NULLABLE;
                case 134:
                    return NOWARN_OP;
                case 133:
                    return NOWARN;
                case 132:
                    return NORMAL_EXAMPLE;
                case 131:
                    return FEASIBLE_BEHAVIOUR;
                case 130:
                    return FEASIBLE_BEHAVIOR;
                case 129:
                    return NORMAL_BEHAVIOUR;
                case 128:
                    return NORMAL_BEHAVIOR;
                case 127:
                    return NON_NULL;
                case 126:
                    return NONNULLELEMENTS;
                case 125:
                    return NEW_OBJECT;
                case 124:
                    return NESTED_CONTRACT_START;
                case 123:
                    return NESTED_CONTRACT_END;
                case 122:
                    return MONITORS_FOR;
                case 121:
                    return MONITORED;
                case 120:
                    return MODIFIES_REDUNDANTLY;
                case 119:
                    return MODIFIES;
                case 118:
                    return LOOP_MODIFIES;
                case 117:
                    return MODIFIABLE_REDUNDANTLY;
                case 116:
                    return MODIFIABLE;
                case 115:
                    return MODEL_PROGRAM;
                case 114:
                    return MODEL;
                case 113:
                    return MIN;
                case 112:
                    return METHOD;
                case 111:
                    return MEASURED_BY_REDUNDANTLY;
                case 110:
                    return ESC_MEASURED_BY;
                case 109:
                    return MEASURED_BY;
                case 108:
                    return MAX;
                case 107:
                    return MAPS_REDUNDANTLY;
                case 106:
                    return MAPS;
                case 105:
                    return MAINTAINING_REDUNDANTLY;
                case 104:
                    return MAINTAINING;
                case 103:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 102:
                    return LOOP_INVARIANT_FREE;
                case 101:
                    return LOOP_INVARIANT;
                case 100:
                    return LOOP_CONTRACT;
                case 99:
                    return LBL;
                case 98:
                    return LBLPOS;
                case 97:
                    return LBLNEG;
                case 96:
                    return JAVA_MATH;
                case 95:
                    return IN_REDUNDANTLY;
                case 94:
                    return INVARIANT_REDUNDANTLY;
                case 93:
                    return NON_NULL_BY_DEFAULT;
                case 92:
                    return NO_STATE;
                case 91:
                    return TWO_STATE;
                case 90:
                    return INSTANCE;
                case 89:
                    return INITIALLY;
                case 88:
                    return INITIALIZER;
                case 87:
                    return IN;
                case 86:
                    return IMPLIES_THAT;
                case 85:
                    return HENCE_BY_REDUNDANTLY;
                case 84:
                    return HENCE_BY;
                case 83:
                    return HELPER;
                case 82:
                    return END;
                case 81:
                    return BEGIN;
                case 80:
                    return GHOST;
                case 79:
                    return READ_ONLY;
                case 78:
                    return REP;
                case 77:
                    return PEER;
                case 76:
                    return FOR_EXAMPLE;
                case 75:
                    return FORALL;
                case 74:
                    return LET;
                case 73:
                    return FORALLQ;
                case 72:
                    return FIELD;
                case 71:
                    return EXTRACT;
                case 70:
                    return EXSURES_REDUNDANTLY;
                case 69:
                    return EXSURES;
                case 68:
                    return EXISTS;
                case 67:
                    return EXCEPTIONAL_EXAMPLE;
                case 66:
                    return EXCEPTIONAL_BEHAVIOUR;
                case 65:
                    return EXCEPTIONAL_BEHAVIOR;
                case 64:
                    return EXAMPLE;
                case 63:
                    return ERASES;
                case 62:
                    return IMPLICATION_BACKWARD;
                case 61:
                    return IMPLICATION;
                case 60:
                    return EQUIVALENCE;
                case 59:
                    return REQUIRES_FREE;
                case 58:
                    return ENSURES_FREE;
                case 57:
                    return ENSURES_REDUNDANTLY;
                case 56:
                    return ENSURES;
                case 55:
                    return DURATION_REDUNDANTLY;
                case 54:
                    return DURATION;
                case 53:
                    return DIVERGES_REDUNDANTLY;
                case 52:
                    return DIVERGES;
                case 51:
                    return DETERMINES;
                case 50:
                    return DECREASING_REDUNDANTLY;
                case 49:
                    return DECREASING;
                case 48:
                    return DECREASES_REDUNDANTLY;
                case 47:
                    return DECREASES;
                case 46:
                    return DECLASSIFIES;
                case 45:
                    return CONTINUE_BEHAVIOUR;
                case 44:
                    return CONTINUE_BEHAVIOR;
                case 43:
                    return CONTINUES_REDUNDANTLY;
                case 42:
                    return CONTINUES;
                case 41:
                    return CONSTRUCTOR;
                case 40:
                    return CONSTRAINT_REDUNDANTLY;
                case 39:
                    return CONSTRAINT;
                case 38:
                    return IMMUTABLE;
                case 37:
                    return CODE_SAFE_MATH;
                case 36:
                    return CODE_JAVA_MATH;
                case 35:
                    return CODE_BIGINT_MATH;
                case 34:
                    return CODE;
                case 33:
                    return CHOOSE_IF;
                case 32:
                    return CHOOSE;
                case 31:
                    return CAPTURES_REDUNDANTLY;
                case 30:
                    return CAPTURES;
                case 29:
                    return CALLABLE_REDUNDANTLY;
                case 28:
                    return CALLABLE;
                case 27:
                    return BREAK_BEHAVIOUR;
                case 26:
                    return BREAK_BEHAVIOR;
                case 25:
                    return BREAKS_REDUNDANTLY;
                case 24:
                    return BREAKS;
                case 23:
                    return BIGINT_MATH;
                case 22:
                    return BIGINT;
                case 21:
                    return BEHAVIOUR;
                case 20:
                    return BEHAVIOR;
                case 19:
                    return AXIOM;
                case 18:
                    return ASSUME_REDUNDANTLY;
                case 17:
                    return ASSUME;
                case 16:
                    return ASSIGNABLE_REDUNDANTLY;
                case 15:
                    return ASSIGNABLE;
                case 14:
                    return ASSERT_REDUNDANTLY;
                case 13:
                    return ANTIVALENCE;
                case 12:
                    return ALSO;
                case 11:
                    return ACCESSIBLE_REDUNDANTLY;
                case 10:
                    return ACCESSIBLE;
                case 9:
                    return MODEL_BEHAVIOUR;
                case 8:
                    return MODEL_BEHAVIOR;
                case 7:
                    return ABRUPT_BEHAVIOUR;
                case 6:
                    return ABRUPT_BEHAVIOR;
                case 5:
                    return INVARIANT;
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
            return this == BYTE
                    || this == CHAR
                    || this == SHORT
                    || this == INT
                    || this == LONG
                    || this == FLOAT
                    || this == DOUBLE;
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
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        JavaToken javaToken = (JavaToken) o;
        if (kind != javaToken.kind) return false;
        if (!text.equals(javaToken.text)) return false;
        return true;
    }
}
