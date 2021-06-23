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
        BY(37),
        CALLABLE(38),
        CALLABLE_REDUNDANTLY(39),
        CAPTURES(40),
        CAPTURES_REDUNDANTLY(41),
        CHOOSE(42),
        CHOOSE_IF(43),
        CODE(44),
        CODE_BIGINT_MATH(45),
        CODE_JAVA_MATH(46),
        CODE_SAFE_MATH(47),
        CONSTRAINT(48),
        CONSTRAINT_REDUNDANTLY(49),
        CONSTRUCTOR(50),
        CONTINUES(51),
        CONTINUES_REDUNDANTLY(52),
        CONTINUE_BEHAVIOR(53),
        CONTINUE_BEHAVIOUR(54),
        DECLASSIFIES(55),
        DECREASES(56),
        DECREASES_REDUNDANTLY(57),
        DECREASING(58),
        DECREASING_REDUNDANTLY(59),
        DETERMINES(60),
        DIVERGES(61),
        DIVERGES_REDUNDANTLY(62),
        DURATION(63),
        DURATION_REDUNDANTLY(64),
        ELEMTYPE(65),
        ENSURES(66),
        ENSURES_REDUNDANTLY(67),
        ENSURES_FREE(68),
        REQUIRES_FREE(69),
        EQUIVALENCE(70),
        IMPLICATION(71),
        IMPLICATION_BACKWARD(72),
        ERASES(73),
        EVERYTHING(74),
        EXAMPLE(75),
        EXCEPTIONAL_BEHAVIOR(76),
        EXCEPTIONAL_BEHAVIOUR(77),
        EXCEPTIONAL_EXAMPLE(78),
        EXISTS(79),
        EXSURES(80),
        EXSURES_REDUNDANTLY(81),
        EXTRACT(82),
        FIELD(83),
        FORALLQ(84),
        FORALL(85),
        FOR_EXAMPLE(86),
        FRESH(87),
        GHOST(88),
        HELPER(89),
        HENCE_by(90),
        HENCE_by_REDUNDANTLY(91),
        IMPLIES_THAT(92),
        IN(93),
        INITIALIZER(94),
        INITIALLY(95),
        INSTANCE(96),
        TWO_STATE(97),
        NO_STATE(98),
        INTO(99),
        INVARIANT_REDUNDANTLY(100),
        INVARIANT_FOR(101),
        IN_REDUNDANTLY(102),
        IS_INITIALIZED(103),
        JAVA_MATH(104),
        LBLNEG(105),
        LBLPOS(106),
        LOCKSET(107),
        LOOP_INVARIANT(108),
        LOOP_INVARIANT_REDUNDANTLY(109),
        MAINTAINING(110),
        MAINTAINING_REDUNDANTLY(111),
        MAPS(112),
        MAPS_REDUNDANTLY(113),
        MAX(114),
        MEASURED_BY(115),
        ESC_MEASURED_BY(116),
        MEASURED_BY_REDUNDANTLY(117),
        METHOD(118),
        MIN(119),
        MODEL(120),
        MODEL_PROGRAM(121),
        MODIFIABLE(122),
        MODIFIABLE_REDUNDANTLY(123),
        MODIFIES(124),
        MODIFIES_REDUNDANTLY(125),
        MONITORED(126),
        MONITORS_FOR(127),
        NESTED_CONTRACT_END(128),
        NESTED_CONTRACT_START(129),
        NEW_OBJECT(130),
        NONNULLELEMENTS(131),
        NON_NULL(132),
        NORMAL_BEHAVIOR(133),
        NORMAL_BEHAVIOUR(134),
        NORMAL_EXAMPLE(135),
        NOTHING(136),
        NOT_ASSIGNED(137),
        NOT_MODIFIED(138),
        NOT_SPECIFIED(139),
        STRICTLY_NOTHING(140),
        NOWARN(141),
        NOWARN_OP(142),
        NULLABLE(143),
        NULLABLE_BY_DEFAULT(144),
        NUM_OF(145),
        OLD_ESC(146),
        OLD(147),
        ONLY_ACCESSED(148),
        ONLY_ASSIGNED(149),
        ONLY_CALLED(150),
        ONLY_CAPTURED(151),
        OR(152),
        POST(153),
        POST_REDUNDANTLY(154),
        PRE_ESC(155),
        PRE(156),
        PRE_REDUNDANTLY(157),
        PRODUCT(158),
        PURE(159),
        REACH(160),
        READABLE(161),
        REAL(162),
        REFINING(163),
        REPRESENTS(164),
        REPRESENTS_REDUNDANTLY(165),
        REQUIRES_REDUNDANTLY(166),
        RESULT(167),
        RETURNS(168),
        RETURNS_REDUNDANTLY(169),
        RETURN_BEHAVIOR(170),
        RETURN_BEHAVIOUR(171),
        SAFE_MATH(172),
        SAME(173),
        SET(174),
        SIGNALS(175),
        SIGNALS_ONLY(176),
        SIGNALS_ONLY_REDUNDANTLY(177),
        SIGNALS_REDUNDANTLY(178),
        SPACE_ESC(179),
        SPEC_BIGINT_MATH(180),
        SPEC_JAVA_MATH(181),
        SPEC_PACKAGE(182),
        SPEC_PRIVATE(183),
        SPEC_PROTECTED(184),
        SPEC_PUBLIC(185),
        SPEC_SAFE_MATH(186),
        STATIC_INITIALIZER(187),
        STRICTLY_PURE(188),
        SUBTYPE(189),
        SUCH_THAT(190),
        SUM(191),
        TYPE(192),
        TYPEOF(193),
        UNINITIALIZED(194),
        UNKNOWN_OP(195),
        UNKNOWN_OP_EQ(196),
        UNREACHABLE(197),
        WARN(198),
        WARN_OP(199),
        WHEN(200),
        WHEN_REDUNDANTLY(201),
        WORKING_SPACE_ESC(202),
        WORKING_SPACE(203),
        WORKING_SPACE_REDUNDANTLY(204),
        WRITABLE(205),
        LOCSET(206),
        STOREREF(207),
        EMPTYSET(208),
        SINGLETON(209),
        STATIC_INVARIANT_FOR(210),
        SETMINUS(211),
        NEWELEMSFRESH(212),
        NEW_OBJECTS(213),
        DISJOINT(214),
        SUBSET(215),
        UNION(216),
        INFINITE_UNION(217),
        INTERSECT(218),
        ENTER_JAVADOC_COMMENT(219),
        ENTER_MULTILINE_COMMENT(220),
        JAVADOC_COMMENT(221),
        MULTI_LINE_COMMENT(222),
        COMMENT_CONTENT(223),
        ABSTRACT(224),
        ASSERT(225),
        BOOLEAN(226),
        BREAK(227),
        BYTE(228),
        CASE(229),
        CATCH(230),
        CHAR(231),
        CLASS(232),
        CONST(233),
        CONTINUE(234),
        _DEFAULT(235),
        DO(236),
        DOUBLE(237),
        ELSE(238),
        ENUM(239),
        EXTENDS(240),
        FALSE(241),
        FINAL(242),
        FINALLY(243),
        FLOAT(244),
        FOR(245),
        GOTO(246),
        IF(247),
        IMPLEMENTS(248),
        IMPORT(249),
        INSTANCEOF(250),
        INT(251),
        INTERFACE(252),
        LONG(253),
        NATIVE(254),
        NEW(255),
        NULL(256),
        PACKAGE(257),
        PRIVATE(258),
        PROTECTED(259),
        PUBLIC(260),
        RECORD(261),
        RETURN(262),
        SHORT(263),
        STATIC(264),
        STRICTFP(265),
        SUPER(266),
        SWITCH(267),
        SYNCHRONIZED(268),
        THIS(269),
        THROW(270),
        THROWS(271),
        TRANSIENT(272),
        TRUE(273),
        TRY(274),
        VOID(275),
        VOLATILE(276),
        WHILE(277),
        YIELD(278),
        REQUIRES(279),
        TO(280),
        WITH(281),
        OPEN(282),
        OPENS(283),
        USES(284),
        MODULE(285),
        EXPORTS(286),
        PROVIDES(287),
        TRANSITIVE(288),
        LONG_LITERAL(289),
        INTEGER_LITERAL(290),
        DECIMAL_LITERAL(291),
        HEX_LITERAL(292),
        OCTAL_LITERAL(293),
        BINARY_LITERAL(294),
        FLOATING_POINT_LITERAL(295),
        DECIMAL_FLOATING_POINT_LITERAL(296),
        DECIMAL_EXPONENT(297),
        HEXADECIMAL_FLOATING_POINT_LITERAL(298),
        HEXADECIMAL_EXPONENT(299),
        HEX_DIGITS(300),
        UNICODE_ESCAPE(301),
        CHARACTER_LITERAL(302),
        STRING_LITERAL(303),
        ENTER_TEXT_BLOCK(304),
        TEXT_BLOCK_LITERAL(305),
        TEXT_BLOCK_CONTENT(306),
        JML_IDENTIFIER(307),
        IDENTIFIER(308),
        LETTER(309),
        PART_LETTER(310),
        LPAREN(311),
        RPAREN(312),
        LBRACE(313),
        RBRACE(314),
        LBRACKET(315),
        RBRACKET(316),
        SEMICOLON(317),
        COMMA(318),
        DOT(319),
        ELLIPSIS(320),
        AT(321),
        DOUBLECOLON(322),
        ASSIGN(323),
        LT(324),
        BANG(325),
        TILDE(326),
        HOOK(327),
        COLON(328),
        ARROW(329),
        EQ(330),
        GE(331),
        LE(332),
        NE(333),
        SC_AND(334),
        SC_OR(335),
        INCR(336),
        DECR(337),
        PLUS(338),
        MINUS(339),
        STAR(340),
        SLASH(341),
        BIT_AND(342),
        BIT_OR(343),
        XOR(344),
        REM(345),
        LSHIFT(346),
        PLUSASSIGN(347),
        MINUSASSIGN(348),
        STARASSIGN(349),
        SLASHASSIGN(350),
        ANDASSIGN(351),
        ORASSIGN(352),
        XORASSIGN(353),
        REMASSIGN(354),
        LSHIFTASSIGN(355),
        RSIGNEDSHIFTASSIGN(356),
        RUNSIGNEDSHIFTASSIGN(357),
        RUNSIGNEDSHIFT(358),
        RSIGNEDSHIFT(359),
        GT(360),
        CTRL_Z(361);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 361:
                    return CTRL_Z;
                case 360:
                    return GT;
                case 359:
                    return RSIGNEDSHIFT;
                case 358:
                    return RUNSIGNEDSHIFT;
                case 357:
                    return RUNSIGNEDSHIFTASSIGN;
                case 356:
                    return RSIGNEDSHIFTASSIGN;
                case 355:
                    return LSHIFTASSIGN;
                case 354:
                    return REMASSIGN;
                case 353:
                    return XORASSIGN;
                case 352:
                    return ORASSIGN;
                case 351:
                    return ANDASSIGN;
                case 350:
                    return SLASHASSIGN;
                case 349:
                    return STARASSIGN;
                case 348:
                    return MINUSASSIGN;
                case 347:
                    return PLUSASSIGN;
                case 346:
                    return LSHIFT;
                case 345:
                    return REM;
                case 344:
                    return XOR;
                case 343:
                    return BIT_OR;
                case 342:
                    return BIT_AND;
                case 341:
                    return SLASH;
                case 340:
                    return STAR;
                case 339:
                    return MINUS;
                case 338:
                    return PLUS;
                case 337:
                    return DECR;
                case 336:
                    return INCR;
                case 335:
                    return SC_OR;
                case 334:
                    return SC_AND;
                case 333:
                    return NE;
                case 332:
                    return LE;
                case 331:
                    return GE;
                case 330:
                    return EQ;
                case 329:
                    return ARROW;
                case 328:
                    return COLON;
                case 327:
                    return HOOK;
                case 326:
                    return TILDE;
                case 325:
                    return BANG;
                case 324:
                    return LT;
                case 323:
                    return ASSIGN;
                case 322:
                    return DOUBLECOLON;
                case 321:
                    return AT;
                case 320:
                    return ELLIPSIS;
                case 319:
                    return DOT;
                case 318:
                    return COMMA;
                case 317:
                    return SEMICOLON;
                case 316:
                    return RBRACKET;
                case 315:
                    return LBRACKET;
                case 314:
                    return RBRACE;
                case 313:
                    return LBRACE;
                case 312:
                    return RPAREN;
                case 311:
                    return LPAREN;
                case 310:
                    return PART_LETTER;
                case 309:
                    return LETTER;
                case 308:
                    return IDENTIFIER;
                case 307:
                    return JML_IDENTIFIER;
                case 306:
                    return TEXT_BLOCK_CONTENT;
                case 305:
                    return TEXT_BLOCK_LITERAL;
                case 304:
                    return ENTER_TEXT_BLOCK;
                case 303:
                    return STRING_LITERAL;
                case 302:
                    return CHARACTER_LITERAL;
                case 301:
                    return UNICODE_ESCAPE;
                case 300:
                    return HEX_DIGITS;
                case 299:
                    return HEXADECIMAL_EXPONENT;
                case 298:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 297:
                    return DECIMAL_EXPONENT;
                case 296:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 295:
                    return FLOATING_POINT_LITERAL;
                case 294:
                    return BINARY_LITERAL;
                case 293:
                    return OCTAL_LITERAL;
                case 292:
                    return HEX_LITERAL;
                case 291:
                    return DECIMAL_LITERAL;
                case 290:
                    return INTEGER_LITERAL;
                case 289:
                    return LONG_LITERAL;
                case 288:
                    return TRANSITIVE;
                case 287:
                    return PROVIDES;
                case 286:
                    return EXPORTS;
                case 285:
                    return MODULE;
                case 284:
                    return USES;
                case 283:
                    return OPENS;
                case 282:
                    return OPEN;
                case 281:
                    return WITH;
                case 280:
                    return TO;
                case 279:
                    return REQUIRES;
                case 278:
                    return YIELD;
                case 277:
                    return WHILE;
                case 276:
                    return VOLATILE;
                case 275:
                    return VOID;
                case 274:
                    return TRY;
                case 273:
                    return TRUE;
                case 272:
                    return TRANSIENT;
                case 271:
                    return THROWS;
                case 270:
                    return THROW;
                case 269:
                    return THIS;
                case 268:
                    return SYNCHRONIZED;
                case 267:
                    return SWITCH;
                case 266:
                    return SUPER;
                case 265:
                    return STRICTFP;
                case 264:
                    return STATIC;
                case 263:
                    return SHORT;
                case 262:
                    return RETURN;
                case 261:
                    return RECORD;
                case 260:
                    return PUBLIC;
                case 259:
                    return PROTECTED;
                case 258:
                    return PRIVATE;
                case 257:
                    return PACKAGE;
                case 256:
                    return NULL;
                case 255:
                    return NEW;
                case 254:
                    return NATIVE;
                case 253:
                    return LONG;
                case 252:
                    return INTERFACE;
                case 251:
                    return INT;
                case 250:
                    return INSTANCEOF;
                case 249:
                    return IMPORT;
                case 248:
                    return IMPLEMENTS;
                case 247:
                    return IF;
                case 246:
                    return GOTO;
                case 245:
                    return FOR;
                case 244:
                    return FLOAT;
                case 243:
                    return FINALLY;
                case 242:
                    return FINAL;
                case 241:
                    return FALSE;
                case 240:
                    return EXTENDS;
                case 239:
                    return ENUM;
                case 238:
                    return ELSE;
                case 237:
                    return DOUBLE;
                case 236:
                    return DO;
                case 235:
                    return _DEFAULT;
                case 234:
                    return CONTINUE;
                case 233:
                    return CONST;
                case 232:
                    return CLASS;
                case 231:
                    return CHAR;
                case 230:
                    return CATCH;
                case 229:
                    return CASE;
                case 228:
                    return BYTE;
                case 227:
                    return BREAK;
                case 226:
                    return BOOLEAN;
                case 225:
                    return ASSERT;
                case 224:
                    return ABSTRACT;
                case 223:
                    return COMMENT_CONTENT;
                case 222:
                    return MULTI_LINE_COMMENT;
                case 221:
                    return JAVADOC_COMMENT;
                case 220:
                    return ENTER_MULTILINE_COMMENT;
                case 219:
                    return ENTER_JAVADOC_COMMENT;
                case 218:
                    return INTERSECT;
                case 217:
                    return INFINITE_UNION;
                case 216:
                    return UNION;
                case 215:
                    return SUBSET;
                case 214:
                    return DISJOINT;
                case 213:
                    return NEW_OBJECTS;
                case 212:
                    return NEWELEMSFRESH;
                case 211:
                    return SETMINUS;
                case 210:
                    return STATIC_INVARIANT_FOR;
                case 209:
                    return SINGLETON;
                case 208:
                    return EMPTYSET;
                case 207:
                    return STOREREF;
                case 206:
                    return LOCSET;
                case 205:
                    return WRITABLE;
                case 204:
                    return WORKING_SPACE_REDUNDANTLY;
                case 203:
                    return WORKING_SPACE;
                case 202:
                    return WORKING_SPACE_ESC;
                case 201:
                    return WHEN_REDUNDANTLY;
                case 200:
                    return WHEN;
                case 199:
                    return WARN_OP;
                case 198:
                    return WARN;
                case 197:
                    return UNREACHABLE;
                case 196:
                    return UNKNOWN_OP_EQ;
                case 195:
                    return UNKNOWN_OP;
                case 194:
                    return UNINITIALIZED;
                case 193:
                    return TYPEOF;
                case 192:
                    return TYPE;
                case 191:
                    return SUM;
                case 190:
                    return SUCH_THAT;
                case 189:
                    return SUBTYPE;
                case 188:
                    return STRICTLY_PURE;
                case 187:
                    return STATIC_INITIALIZER;
                case 186:
                    return SPEC_SAFE_MATH;
                case 185:
                    return SPEC_PUBLIC;
                case 184:
                    return SPEC_PROTECTED;
                case 183:
                    return SPEC_PRIVATE;
                case 182:
                    return SPEC_PACKAGE;
                case 181:
                    return SPEC_JAVA_MATH;
                case 180:
                    return SPEC_BIGINT_MATH;
                case 179:
                    return SPACE_ESC;
                case 178:
                    return SIGNALS_REDUNDANTLY;
                case 177:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 176:
                    return SIGNALS_ONLY;
                case 175:
                    return SIGNALS;
                case 174:
                    return SET;
                case 173:
                    return SAME;
                case 172:
                    return SAFE_MATH;
                case 171:
                    return RETURN_BEHAVIOUR;
                case 170:
                    return RETURN_BEHAVIOR;
                case 169:
                    return RETURNS_REDUNDANTLY;
                case 168:
                    return RETURNS;
                case 167:
                    return RESULT;
                case 166:
                    return REQUIRES_REDUNDANTLY;
                case 165:
                    return REPRESENTS_REDUNDANTLY;
                case 164:
                    return REPRESENTS;
                case 163:
                    return REFINING;
                case 162:
                    return REAL;
                case 161:
                    return READABLE;
                case 160:
                    return REACH;
                case 159:
                    return PURE;
                case 158:
                    return PRODUCT;
                case 157:
                    return PRE_REDUNDANTLY;
                case 156:
                    return PRE;
                case 155:
                    return PRE_ESC;
                case 154:
                    return POST_REDUNDANTLY;
                case 153:
                    return POST;
                case 152:
                    return OR;
                case 151:
                    return ONLY_CAPTURED;
                case 150:
                    return ONLY_CALLED;
                case 149:
                    return ONLY_ASSIGNED;
                case 148:
                    return ONLY_ACCESSED;
                case 147:
                    return OLD;
                case 146:
                    return OLD_ESC;
                case 145:
                    return NUM_OF;
                case 144:
                    return NULLABLE_BY_DEFAULT;
                case 143:
                    return NULLABLE;
                case 142:
                    return NOWARN_OP;
                case 141:
                    return NOWARN;
                case 140:
                    return STRICTLY_NOTHING;
                case 139:
                    return NOT_SPECIFIED;
                case 138:
                    return NOT_MODIFIED;
                case 137:
                    return NOT_ASSIGNED;
                case 136:
                    return NOTHING;
                case 135:
                    return NORMAL_EXAMPLE;
                case 134:
                    return NORMAL_BEHAVIOUR;
                case 133:
                    return NORMAL_BEHAVIOR;
                case 132:
                    return NON_NULL;
                case 131:
                    return NONNULLELEMENTS;
                case 130:
                    return NEW_OBJECT;
                case 129:
                    return NESTED_CONTRACT_START;
                case 128:
                    return NESTED_CONTRACT_END;
                case 127:
                    return MONITORS_FOR;
                case 126:
                    return MONITORED;
                case 125:
                    return MODIFIES_REDUNDANTLY;
                case 124:
                    return MODIFIES;
                case 123:
                    return MODIFIABLE_REDUNDANTLY;
                case 122:
                    return MODIFIABLE;
                case 121:
                    return MODEL_PROGRAM;
                case 120:
                    return MODEL;
                case 119:
                    return MIN;
                case 118:
                    return METHOD;
                case 117:
                    return MEASURED_BY_REDUNDANTLY;
                case 116:
                    return ESC_MEASURED_BY;
                case 115:
                    return MEASURED_BY;
                case 114:
                    return MAX;
                case 113:
                    return MAPS_REDUNDANTLY;
                case 112:
                    return MAPS;
                case 111:
                    return MAINTAINING_REDUNDANTLY;
                case 110:
                    return MAINTAINING;
                case 109:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 108:
                    return LOOP_INVARIANT;
                case 107:
                    return LOCKSET;
                case 106:
                    return LBLPOS;
                case 105:
                    return LBLNEG;
                case 104:
                    return JAVA_MATH;
                case 103:
                    return IS_INITIALIZED;
                case 102:
                    return IN_REDUNDANTLY;
                case 101:
                    return INVARIANT_FOR;
                case 100:
                    return INVARIANT_REDUNDANTLY;
                case 99:
                    return INTO;
                case 98:
                    return NO_STATE;
                case 97:
                    return TWO_STATE;
                case 96:
                    return INSTANCE;
                case 95:
                    return INITIALLY;
                case 94:
                    return INITIALIZER;
                case 93:
                    return IN;
                case 92:
                    return IMPLIES_THAT;
                case 91:
                    return HENCE_by_REDUNDANTLY;
                case 90:
                    return HENCE_by;
                case 89:
                    return HELPER;
                case 88:
                    return GHOST;
                case 87:
                    return FRESH;
                case 86:
                    return FOR_EXAMPLE;
                case 85:
                    return FORALL;
                case 84:
                    return FORALLQ;
                case 83:
                    return FIELD;
                case 82:
                    return EXTRACT;
                case 81:
                    return EXSURES_REDUNDANTLY;
                case 80:
                    return EXSURES;
                case 79:
                    return EXISTS;
                case 78:
                    return EXCEPTIONAL_EXAMPLE;
                case 77:
                    return EXCEPTIONAL_BEHAVIOUR;
                case 76:
                    return EXCEPTIONAL_BEHAVIOR;
                case 75:
                    return EXAMPLE;
                case 74:
                    return EVERYTHING;
                case 73:
                    return ERASES;
                case 72:
                    return IMPLICATION_BACKWARD;
                case 71:
                    return IMPLICATION;
                case 70:
                    return EQUIVALENCE;
                case 69:
                    return REQUIRES_FREE;
                case 68:
                    return ENSURES_FREE;
                case 67:
                    return ENSURES_REDUNDANTLY;
                case 66:
                    return ENSURES;
                case 65:
                    return ELEMTYPE;
                case 64:
                    return DURATION_REDUNDANTLY;
                case 63:
                    return DURATION;
                case 62:
                    return DIVERGES_REDUNDANTLY;
                case 61:
                    return DIVERGES;
                case 60:
                    return DETERMINES;
                case 59:
                    return DECREASING_REDUNDANTLY;
                case 58:
                    return DECREASING;
                case 57:
                    return DECREASES_REDUNDANTLY;
                case 56:
                    return DECREASES;
                case 55:
                    return DECLASSIFIES;
                case 54:
                    return CONTINUE_BEHAVIOUR;
                case 53:
                    return CONTINUE_BEHAVIOR;
                case 52:
                    return CONTINUES_REDUNDANTLY;
                case 51:
                    return CONTINUES;
                case 50:
                    return CONSTRUCTOR;
                case 49:
                    return CONSTRAINT_REDUNDANTLY;
                case 48:
                    return CONSTRAINT;
                case 47:
                    return CODE_SAFE_MATH;
                case 46:
                    return CODE_JAVA_MATH;
                case 45:
                    return CODE_BIGINT_MATH;
                case 44:
                    return CODE;
                case 43:
                    return CHOOSE_IF;
                case 42:
                    return CHOOSE;
                case 41:
                    return CAPTURES_REDUNDANTLY;
                case 40:
                    return CAPTURES;
                case 39:
                    return CALLABLE_REDUNDANTLY;
                case 38:
                    return CALLABLE;
                case 37:
                    return BY;
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
