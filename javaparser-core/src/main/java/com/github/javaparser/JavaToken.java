/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
        INVARIANT(5),
        ABRUPT_BEHAVIOR(6),
        ABRUPT_BEHAVIOUR(7),
        MODEL_BEHAVIOR(8),
        MODEL_BEHAVIOUR(9),
        ACCESSIBLE(10),
        ACCESSIBLE_REDUNDANTLY(11),
        ALSO(12),
        ANTIVALENCE(13),
        JML_ASSERT(14),
        ASSERT_REDUNDANTLY(15),
        ASSIGNABLE(16),
        ASSIGNABLE_REDUNDANTLY(17),
        ASSUME(18),
        ASSUME_REDUNDANTLY(19),
        AXIOM(20),
        BEHAVIOR(21),
        BEHAVIOUR(22),
        BIGINT(23),
        BIGINT_MATH(24),
        BREAKS(25),
        BREAKS_REDUNDANTLY(26),
        BREAK_BEHAVIOR(27),
        BREAK_BEHAVIOUR(28),
        CALLABLE(29),
        CALLABLE_REDUNDANTLY(30),
        CAPTURES(31),
        CAPTURES_REDUNDANTLY(32),
        CHOOSE(33),
        CHOOSE_IF(34),
        CODE(35),
        CODE_BIGINT_MATH(36),
        CODE_JAVA_MATH(37),
        CODE_SAFE_MATH(38),
        IMMUTABLE(39),
        CONSTRAINT(40),
        CONSTRAINT_REDUNDANTLY(41),
        CONSTRUCTOR(42),
        CONTINUES(43),
        CONTINUES_REDUNDANTLY(44),
        CONTINUE_BEHAVIOR(45),
        CONTINUE_BEHAVIOUR(46),
        DECLASSIFIES(47),
        DECREASES(48),
        DECREASES_REDUNDANTLY(49),
        DECREASING(50),
        DECREASING_REDUNDANTLY(51),
        DETERMINES(52),
        LOOP_DETERMINES(53),
        SEPARATES(54),
        LOOP_SEPARATES(55),
        NEW_OBJECTS(56),
        BY(57),
        DIVERGES(58),
        DIVERGES_REDUNDANTLY(59),
        DURATION(60),
        DURATION_REDUNDANTLY(61),
        ENSURES(62),
        ENSURES_REDUNDANTLY(63),
        ENSURES_FREE(64),
        REQUIRES_FREE(65),
        EQUIVALENCE(66),
        IMPLICATION(67),
        IMPLICATION_BACKWARD(68),
        ERASES(69),
        EXAMPLE(70),
        EXCEPTIONAL_BEHAVIOR(71),
        EXCEPTIONAL_BEHAVIOUR(72),
        EXCEPTIONAL_EXAMPLE(73),
        EXISTS(74),
        EXSURES(75),
        EXSURES_REDUNDANTLY(76),
        EXTRACT(77),
        FIELD(78),
        FORALLQ(79),
        LET(80),
        FORALL(81),
        FOR_EXAMPLE(82),
        PEER(83),
        REP(84),
        READ_ONLY(85),
        GHOST(86),
        BEGIN(87),
        END(88),
        HELPER(89),
        HENCE_BY(90),
        HENCE_BY_REDUNDANTLY(91),
        IMPLIES_THAT(92),
        IN(93),
        INITIALIZER(94),
        INITIALLY(95),
        INSTANCE(96),
        TWO_STATE(97),
        NO_STATE(98),
        NON_NULL_BY_DEFAULT(99),
        INVARIANT_REDUNDANTLY(100),
        IN_REDUNDANTLY(101),
        JAVA_MATH(102),
        LBLNEG(103),
        LBLPOS(104),
        LBL(105),
        LOOP_CONTRACT(106),
        LOOP_INVARIANT(107),
        LOOP_INVARIANT_FREE(108),
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
        LOOP_MODIFIES(124),
        MODIFIES(125),
        MODIFIES_REDUNDANTLY(126),
        MONITORED(127),
        MONITORS_FOR(128),
        NESTED_CONTRACT_END(129),
        NESTED_CONTRACT_START(130),
        NONNULLELEMENTS(131),
        NON_NULL(132),
        NORMAL_BEHAVIOR(133),
        NORMAL_BEHAVIOUR(134),
        FEASIBLE_BEHAVIOR(135),
        FEASIBLE_BEHAVIOUR(136),
        NORMAL_EXAMPLE(137),
        NOWARN(138),
        NOWARN_OP(139),
        NULLABLE(140),
        NULLABLE_BY_DEFAULT(141),
        NUM_OF(142),
        OLD(143),
        OR(144),
        POST(145),
        POST_REDUNDANTLY(146),
        PRE_ESC(147),
        PRE(148),
        PRE_REDUNDANTLY(149),
        PRODUCT(150),
        PURE(151),
        READABLE(152),
        REFINING(153),
        REPRESENTS(154),
        REPRESENTS_REDUNDANTLY(155),
        REQUIRES_REDUNDANTLY(156),
        RESULT(157),
        RETURNS(158),
        RETURNS_REDUNDANTLY(159),
        RETURN_BEHAVIOR(160),
        BACKARROW(161),
        RETURN_BEHAVIOUR(162),
        SAFE_MATH(163),
        SET(164),
        SIGNALS(165),
        SIGNALS_ONLY(166),
        SIGNALS_ONLY_REDUNDANTLY(167),
        SIGNALS_REDUNDANTLY(168),
        SPEC_BIGINT_MATH(169),
        SPEC_JAVA_MATH(170),
        SPEC_PACKAGE(171),
        SPEC_PRIVATE(172),
        SPEC_PROTECTED(173),
        SPEC_PUBLIC(174),
        SPEC_SAFE_MATH(175),
        STATIC_INITIALIZER(176),
        STRICTLY_PURE(177),
        SUBTYPE(178),
        SUCH_THAT(179),
        SUM(180),
        TYPE(181),
        UNINITIALIZED(182),
        UNKNOWN_OP(183),
        UNKNOWN_OP_EQ(184),
        UNREACHABLE(185),
        WARN(186),
        WARN_OP(187),
        WHEN_REDUNDANTLY(188),
        WORKING_SPACE_ESC(189),
        WORKING_SPACE(190),
        WORKING_SPACE_REDUNDANTLY(191),
        WRITABLE(192),
        JML_LINE_COMMENT(193),
        SINGLE_LINE_COMMENT(194),
        JML_ENTER_MULTILINE_COMMENT(195),
        ENTER_JAVADOC_COMMENT(196),
        ENTER_JML_BLOCK_COMMENT(197),
        ENTER_MULTILINE_COMMENT(198),
        JML_BLOCK_COMMENT(199),
        JAVADOC_COMMENT(200),
        MULTI_LINE_COMMENT(201),
        JML_MULTI_LINE_COMMENT(202),
        COMMENT_CONTENT(203),
        ASSERT(204),
        ABSTRACT(205),
        BOOLEAN(206),
        BREAK(207),
        BYTE(208),
        CASE(209),
        CATCH(210),
        CHAR(211),
        CLASS(212),
        CONST(213),
        CONTINUE(214),
        _DEFAULT(215),
        DO(216),
        DOUBLE(217),
        ELSE(218),
        ENUM(219),
        EXTENDS(220),
        FALSE(221),
        FINAL(222),
        FINALLY(223),
        FLOAT(224),
        FOR(225),
        GOTO(226),
        IF(227),
        IMPLEMENTS(228),
        IMPORT(229),
        INSTANCEOF(230),
        INT(231),
        INTERFACE(232),
        LONG(233),
        NATIVE(234),
        NEW(235),
        NON_SEALED(236),
        NULL(237),
        PACKAGE(238),
        PERMITS(239),
        PRIVATE(240),
        PROTECTED(241),
        PUBLIC(242),
        RECORD(243),
        RETURN(244),
        SEALED(245),
        SHORT(246),
        STATIC(247),
        STRICTFP(248),
        SUPER(249),
        SWITCH(250),
        SYNCHRONIZED(251),
        THIS(252),
        THROW(253),
        THROWS(254),
        TRANSIENT(255),
        TRUE(256),
        TRY(257),
        VOID(258),
        VOLATILE(259),
        WHILE(260),
        YIELD(261),
        REQUIRES(262),
        TO(263),
        WITH(264),
        OPEN(265),
        OPENS(266),
        USES(267),
        MODULE(268),
        EXPORTS(269),
        PROVIDES(270),
        TRANSITIVE(271),
        WHEN(272),
        SOURCE(273),
        TRANSACTIONBEGIN(274),
        TRANSACTIONCOMMIT(275),
        TRANSACTIONFINISH(276),
        TRANSACTIONABORT(277),
        RETURNTYPE(278),
        LOOPSCOPE(279),
        MERGE_POINT(280),
        METHODFRAME(281),
        EXEC(282),
        CONTINUETYPE(283),
        CCATCH(284),
        CCAT(285),
        BREAKTYPE(286),
        TYPEOF(287),
        SWITCHTOIF(288),
        UNPACK(289),
        REATTACHLOOPINVARIANT(290),
        FORINITUNFOLDTRANSFORMER(291),
        LOOPSCOPEINVARIANTTRANSFORMER(292),
        SETSV(293),
        ISSTATIC(294),
        EVALARGS(295),
        REPLACEARGS(296),
        UNWINDLOOP(297),
        CATCHALL(298),
        COMMIT(299),
        FINISH(300),
        ABORT(301),
        UNWIND_LOOP_BOUNDED(302),
        FORTOWHILE(303),
        DOBREAK(304),
        METHODCALL(305),
        EXPANDMETHODBODY(306),
        CONSTRUCTORCALL(307),
        SPECIALCONSTRUCTORECALL(308),
        POSTWORK(309),
        STATICINITIALIZATION(310),
        RESOLVE_MULTIPLE_VAR_DECL(311),
        ARRAY_POST_DECL(312),
        ARRAY_INIT_CREATION(313),
        ARRAY_INIT_CREATION_TRANSIENT(314),
        ARRAY_INIT_CREATION_ASSIGNMENTS(315),
        ENHANCEDFOR_ELIM(316),
        STATIC_EVALUATE(317),
        CREATE_OBJECT(318),
        LENGTHREF(319),
        RESULTARROW(320),
        LONG_LITERAL(321),
        INTEGER_LITERAL(322),
        DECIMAL_LITERAL(323),
        HEX_LITERAL(324),
        OCTAL_LITERAL(325),
        BINARY_LITERAL(326),
        FLOATING_POINT_LITERAL(327),
        DECIMAL_FLOATING_POINT_LITERAL(328),
        DECIMAL_EXPONENT(329),
        HEXADECIMAL_FLOATING_POINT_LITERAL(330),
        HEXADECIMAL_EXPONENT(331),
        HEX_DIGITS(332),
        UNICODE_ESCAPE(333),
        CHARACTER_LITERAL(334),
        STRING_LITERAL(335),
        ENTER_TEXT_BLOCK(336),
        TEXT_BLOCK_LITERAL(337),
        TEXT_BLOCK_CONTENT(338),
        IDENTIFIER(339),
        JML_IDENTIFIER(340),
        SVIDENTIFIER(341),
        KEYIDENTIFIER(342),
        NON_UNDERSCORE_LETTER(343),
        PART_LETTER(344),
        LPAREN(345),
        RPAREN(346),
        LBRACE(347),
        RBRACE(348),
        LBRACKET(349),
        RBRACKET(350),
        SEMICOLON(351),
        COMMA(352),
        DOTDOT(353),
        ELLIPSIS(354),
        DOT(355),
        AT(356),
        DOUBLECOLON(357),
        ASSIGN(358),
        LT(359),
        BANG(360),
        TILDE(361),
        HOOK(362),
        COLON(363),
        ARROW(364),
        EQ(365),
        GE(366),
        LE(367),
        NE(368),
        SC_AND(369),
        SC_OR(370),
        INCR(371),
        DECR(372),
        PLUS(373),
        MINUS(374),
        STAR(375),
        SLASH(376),
        BIT_AND(377),
        BIT_OR(378),
        XOR(379),
        REM(380),
        LSHIFT(381),
        SHARP(382),
        PLUSASSIGN(383),
        MINUSASSIGN(384),
        STARASSIGN(385),
        SLASHASSIGN(386),
        ANDASSIGN(387),
        ORASSIGN(388),
        XORASSIGN(389),
        REMASSIGN(390),
        LSHIFTASSIGN(391),
        RSIGNEDSHIFTASSIGN(392),
        RUNSIGNEDSHIFTASSIGN(393),
        RUNSIGNEDSHIFT(394),
        RSIGNEDSHIFT(395),
        GT(396),
        CTRL_Z(397),
        UNNAMED_PLACEHOLDER(398);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 398:
                    return UNNAMED_PLACEHOLDER;
                case 397:
                    return CTRL_Z;
                case 396:
                    return GT;
                case 395:
                    return RSIGNEDSHIFT;
                case 394:
                    return RUNSIGNEDSHIFT;
                case 393:
                    return RUNSIGNEDSHIFTASSIGN;
                case 392:
                    return RSIGNEDSHIFTASSIGN;
                case 391:
                    return LSHIFTASSIGN;
                case 390:
                    return REMASSIGN;
                case 389:
                    return XORASSIGN;
                case 388:
                    return ORASSIGN;
                case 387:
                    return ANDASSIGN;
                case 386:
                    return SLASHASSIGN;
                case 385:
                    return STARASSIGN;
                case 384:
                    return MINUSASSIGN;
                case 383:
                    return PLUSASSIGN;
                case 382:
                    return SHARP;
                case 381:
                    return LSHIFT;
                case 380:
                    return REM;
                case 379:
                    return XOR;
                case 378:
                    return BIT_OR;
                case 377:
                    return BIT_AND;
                case 376:
                    return SLASH;
                case 375:
                    return STAR;
                case 374:
                    return MINUS;
                case 373:
                    return PLUS;
                case 372:
                    return DECR;
                case 371:
                    return INCR;
                case 370:
                    return SC_OR;
                case 369:
                    return SC_AND;
                case 368:
                    return NE;
                case 367:
                    return LE;
                case 366:
                    return GE;
                case 365:
                    return EQ;
                case 364:
                    return ARROW;
                case 363:
                    return COLON;
                case 362:
                    return HOOK;
                case 361:
                    return TILDE;
                case 360:
                    return BANG;
                case 359:
                    return LT;
                case 358:
                    return ASSIGN;
                case 357:
                    return DOUBLECOLON;
                case 356:
                    return AT;
                case 355:
                    return DOT;
                case 354:
                    return ELLIPSIS;
                case 353:
                    return DOTDOT;
                case 352:
                    return COMMA;
                case 351:
                    return SEMICOLON;
                case 350:
                    return RBRACKET;
                case 349:
                    return LBRACKET;
                case 348:
                    return RBRACE;
                case 347:
                    return LBRACE;
                case 346:
                    return RPAREN;
                case 345:
                    return LPAREN;
                case 344:
                    return PART_LETTER;
                case 343:
                    return NON_UNDERSCORE_LETTER;
                case 342:
                    return KEYIDENTIFIER;
                case 341:
                    return SVIDENTIFIER;
                case 340:
                    return JML_IDENTIFIER;
                case 339:
                    return IDENTIFIER;
                case 338:
                    return TEXT_BLOCK_CONTENT;
                case 337:
                    return TEXT_BLOCK_LITERAL;
                case 336:
                    return ENTER_TEXT_BLOCK;
                case 335:
                    return STRING_LITERAL;
                case 334:
                    return CHARACTER_LITERAL;
                case 333:
                    return UNICODE_ESCAPE;
                case 332:
                    return HEX_DIGITS;
                case 331:
                    return HEXADECIMAL_EXPONENT;
                case 330:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 329:
                    return DECIMAL_EXPONENT;
                case 328:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 327:
                    return FLOATING_POINT_LITERAL;
                case 326:
                    return BINARY_LITERAL;
                case 325:
                    return OCTAL_LITERAL;
                case 324:
                    return HEX_LITERAL;
                case 323:
                    return DECIMAL_LITERAL;
                case 322:
                    return INTEGER_LITERAL;
                case 321:
                    return LONG_LITERAL;
                case 320:
                    return RESULTARROW;
                case 319:
                    return LENGTHREF;
                case 318:
                    return CREATE_OBJECT;
                case 317:
                    return STATIC_EVALUATE;
                case 316:
                    return ENHANCEDFOR_ELIM;
                case 315:
                    return ARRAY_INIT_CREATION_ASSIGNMENTS;
                case 314:
                    return ARRAY_INIT_CREATION_TRANSIENT;
                case 313:
                    return ARRAY_INIT_CREATION;
                case 312:
                    return ARRAY_POST_DECL;
                case 311:
                    return RESOLVE_MULTIPLE_VAR_DECL;
                case 310:
                    return STATICINITIALIZATION;
                case 309:
                    return POSTWORK;
                case 308:
                    return SPECIALCONSTRUCTORECALL;
                case 307:
                    return CONSTRUCTORCALL;
                case 306:
                    return EXPANDMETHODBODY;
                case 305:
                    return METHODCALL;
                case 304:
                    return DOBREAK;
                case 303:
                    return FORTOWHILE;
                case 302:
                    return UNWIND_LOOP_BOUNDED;
                case 301:
                    return ABORT;
                case 300:
                    return FINISH;
                case 299:
                    return COMMIT;
                case 298:
                    return CATCHALL;
                case 297:
                    return UNWINDLOOP;
                case 296:
                    return REPLACEARGS;
                case 295:
                    return EVALARGS;
                case 294:
                    return ISSTATIC;
                case 293:
                    return SETSV;
                case 292:
                    return LOOPSCOPEINVARIANTTRANSFORMER;
                case 291:
                    return FORINITUNFOLDTRANSFORMER;
                case 290:
                    return REATTACHLOOPINVARIANT;
                case 289:
                    return UNPACK;
                case 288:
                    return SWITCHTOIF;
                case 287:
                    return TYPEOF;
                case 286:
                    return BREAKTYPE;
                case 285:
                    return CCAT;
                case 284:
                    return CCATCH;
                case 283:
                    return CONTINUETYPE;
                case 282:
                    return EXEC;
                case 281:
                    return METHODFRAME;
                case 280:
                    return MERGE_POINT;
                case 279:
                    return LOOPSCOPE;
                case 278:
                    return RETURNTYPE;
                case 277:
                    return TRANSACTIONABORT;
                case 276:
                    return TRANSACTIONFINISH;
                case 275:
                    return TRANSACTIONCOMMIT;
                case 274:
                    return TRANSACTIONBEGIN;
                case 273:
                    return SOURCE;
                case 272:
                    return WHEN;
                case 271:
                    return TRANSITIVE;
                case 270:
                    return PROVIDES;
                case 269:
                    return EXPORTS;
                case 268:
                    return MODULE;
                case 267:
                    return USES;
                case 266:
                    return OPENS;
                case 265:
                    return OPEN;
                case 264:
                    return WITH;
                case 263:
                    return TO;
                case 262:
                    return REQUIRES;
                case 261:
                    return YIELD;
                case 260:
                    return WHILE;
                case 259:
                    return VOLATILE;
                case 258:
                    return VOID;
                case 257:
                    return TRY;
                case 256:
                    return TRUE;
                case 255:
                    return TRANSIENT;
                case 254:
                    return THROWS;
                case 253:
                    return THROW;
                case 252:
                    return THIS;
                case 251:
                    return SYNCHRONIZED;
                case 250:
                    return SWITCH;
                case 249:
                    return SUPER;
                case 248:
                    return STRICTFP;
                case 247:
                    return STATIC;
                case 246:
                    return SHORT;
                case 245:
                    return SEALED;
                case 244:
                    return RETURN;
                case 243:
                    return RECORD;
                case 242:
                    return PUBLIC;
                case 241:
                    return PROTECTED;
                case 240:
                    return PRIVATE;
                case 239:
                    return PERMITS;
                case 238:
                    return PACKAGE;
                case 237:
                    return NULL;
                case 236:
                    return NON_SEALED;
                case 235:
                    return NEW;
                case 234:
                    return NATIVE;
                case 233:
                    return LONG;
                case 232:
                    return INTERFACE;
                case 231:
                    return INT;
                case 230:
                    return INSTANCEOF;
                case 229:
                    return IMPORT;
                case 228:
                    return IMPLEMENTS;
                case 227:
                    return IF;
                case 226:
                    return GOTO;
                case 225:
                    return FOR;
                case 224:
                    return FLOAT;
                case 223:
                    return FINALLY;
                case 222:
                    return FINAL;
                case 221:
                    return FALSE;
                case 220:
                    return EXTENDS;
                case 219:
                    return ENUM;
                case 218:
                    return ELSE;
                case 217:
                    return DOUBLE;
                case 216:
                    return DO;
                case 215:
                    return _DEFAULT;
                case 214:
                    return CONTINUE;
                case 213:
                    return CONST;
                case 212:
                    return CLASS;
                case 211:
                    return CHAR;
                case 210:
                    return CATCH;
                case 209:
                    return CASE;
                case 208:
                    return BYTE;
                case 207:
                    return BREAK;
                case 206:
                    return BOOLEAN;
                case 205:
                    return ABSTRACT;
                case 204:
                    return ASSERT;
                case 203:
                    return COMMENT_CONTENT;
                case 202:
                    return JML_MULTI_LINE_COMMENT;
                case 201:
                    return MULTI_LINE_COMMENT;
                case 200:
                    return JAVADOC_COMMENT;
                case 199:
                    return JML_BLOCK_COMMENT;
                case 198:
                    return ENTER_MULTILINE_COMMENT;
                case 197:
                    return ENTER_JML_BLOCK_COMMENT;
                case 196:
                    return ENTER_JAVADOC_COMMENT;
                case 195:
                    return JML_ENTER_MULTILINE_COMMENT;
                case 194:
                    return SINGLE_LINE_COMMENT;
                case 193:
                    return JML_LINE_COMMENT;
                case 192:
                    return WRITABLE;
                case 191:
                    return WORKING_SPACE_REDUNDANTLY;
                case 190:
                    return WORKING_SPACE;
                case 189:
                    return WORKING_SPACE_ESC;
                case 188:
                    return WHEN_REDUNDANTLY;
                case 187:
                    return WARN_OP;
                case 186:
                    return WARN;
                case 185:
                    return UNREACHABLE;
                case 184:
                    return UNKNOWN_OP_EQ;
                case 183:
                    return UNKNOWN_OP;
                case 182:
                    return UNINITIALIZED;
                case 181:
                    return TYPE;
                case 180:
                    return SUM;
                case 179:
                    return SUCH_THAT;
                case 178:
                    return SUBTYPE;
                case 177:
                    return STRICTLY_PURE;
                case 176:
                    return STATIC_INITIALIZER;
                case 175:
                    return SPEC_SAFE_MATH;
                case 174:
                    return SPEC_PUBLIC;
                case 173:
                    return SPEC_PROTECTED;
                case 172:
                    return SPEC_PRIVATE;
                case 171:
                    return SPEC_PACKAGE;
                case 170:
                    return SPEC_JAVA_MATH;
                case 169:
                    return SPEC_BIGINT_MATH;
                case 168:
                    return SIGNALS_REDUNDANTLY;
                case 167:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 166:
                    return SIGNALS_ONLY;
                case 165:
                    return SIGNALS;
                case 164:
                    return SET;
                case 163:
                    return SAFE_MATH;
                case 162:
                    return RETURN_BEHAVIOUR;
                case 161:
                    return BACKARROW;
                case 160:
                    return RETURN_BEHAVIOR;
                case 159:
                    return RETURNS_REDUNDANTLY;
                case 158:
                    return RETURNS;
                case 157:
                    return RESULT;
                case 156:
                    return REQUIRES_REDUNDANTLY;
                case 155:
                    return REPRESENTS_REDUNDANTLY;
                case 154:
                    return REPRESENTS;
                case 153:
                    return REFINING;
                case 152:
                    return READABLE;
                case 151:
                    return PURE;
                case 150:
                    return PRODUCT;
                case 149:
                    return PRE_REDUNDANTLY;
                case 148:
                    return PRE;
                case 147:
                    return PRE_ESC;
                case 146:
                    return POST_REDUNDANTLY;
                case 145:
                    return POST;
                case 144:
                    return OR;
                case 143:
                    return OLD;
                case 142:
                    return NUM_OF;
                case 141:
                    return NULLABLE_BY_DEFAULT;
                case 140:
                    return NULLABLE;
                case 139:
                    return NOWARN_OP;
                case 138:
                    return NOWARN;
                case 137:
                    return NORMAL_EXAMPLE;
                case 136:
                    return FEASIBLE_BEHAVIOUR;
                case 135:
                    return FEASIBLE_BEHAVIOR;
                case 134:
                    return NORMAL_BEHAVIOUR;
                case 133:
                    return NORMAL_BEHAVIOR;
                case 132:
                    return NON_NULL;
                case 131:
                    return NONNULLELEMENTS;
                case 130:
                    return NESTED_CONTRACT_START;
                case 129:
                    return NESTED_CONTRACT_END;
                case 128:
                    return MONITORS_FOR;
                case 127:
                    return MONITORED;
                case 126:
                    return MODIFIES_REDUNDANTLY;
                case 125:
                    return MODIFIES;
                case 124:
                    return LOOP_MODIFIES;
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
                    return LOOP_INVARIANT_FREE;
                case 107:
                    return LOOP_INVARIANT;
                case 106:
                    return LOOP_CONTRACT;
                case 105:
                    return LBL;
                case 104:
                    return LBLPOS;
                case 103:
                    return LBLNEG;
                case 102:
                    return JAVA_MATH;
                case 101:
                    return IN_REDUNDANTLY;
                case 100:
                    return INVARIANT_REDUNDANTLY;
                case 99:
                    return NON_NULL_BY_DEFAULT;
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
                    return HENCE_BY_REDUNDANTLY;
                case 90:
                    return HENCE_BY;
                case 89:
                    return HELPER;
                case 88:
                    return END;
                case 87:
                    return BEGIN;
                case 86:
                    return GHOST;
                case 85:
                    return READ_ONLY;
                case 84:
                    return REP;
                case 83:
                    return PEER;
                case 82:
                    return FOR_EXAMPLE;
                case 81:
                    return FORALL;
                case 80:
                    return LET;
                case 79:
                    return FORALLQ;
                case 78:
                    return FIELD;
                case 77:
                    return EXTRACT;
                case 76:
                    return EXSURES_REDUNDANTLY;
                case 75:
                    return EXSURES;
                case 74:
                    return EXISTS;
                case 73:
                    return EXCEPTIONAL_EXAMPLE;
                case 72:
                    return EXCEPTIONAL_BEHAVIOUR;
                case 71:
                    return EXCEPTIONAL_BEHAVIOR;
                case 70:
                    return EXAMPLE;
                case 69:
                    return ERASES;
                case 68:
                    return IMPLICATION_BACKWARD;
                case 67:
                    return IMPLICATION;
                case 66:
                    return EQUIVALENCE;
                case 65:
                    return REQUIRES_FREE;
                case 64:
                    return ENSURES_FREE;
                case 63:
                    return ENSURES_REDUNDANTLY;
                case 62:
                    return ENSURES;
                case 61:
                    return DURATION_REDUNDANTLY;
                case 60:
                    return DURATION;
                case 59:
                    return DIVERGES_REDUNDANTLY;
                case 58:
                    return DIVERGES;
                case 57:
                    return BY;
                case 56:
                    return NEW_OBJECTS;
                case 55:
                    return LOOP_SEPARATES;
                case 54:
                    return SEPARATES;
                case 53:
                    return LOOP_DETERMINES;
                case 52:
                    return DETERMINES;
                case 51:
                    return DECREASING_REDUNDANTLY;
                case 50:
                    return DECREASING;
                case 49:
                    return DECREASES_REDUNDANTLY;
                case 48:
                    return DECREASES;
                case 47:
                    return DECLASSIFIES;
                case 46:
                    return CONTINUE_BEHAVIOUR;
                case 45:
                    return CONTINUE_BEHAVIOR;
                case 44:
                    return CONTINUES_REDUNDANTLY;
                case 43:
                    return CONTINUES;
                case 42:
                    return CONSTRUCTOR;
                case 41:
                    return CONSTRAINT_REDUNDANTLY;
                case 40:
                    return CONSTRAINT;
                case 39:
                    return IMMUTABLE;
                case 38:
                    return CODE_SAFE_MATH;
                case 37:
                    return CODE_JAVA_MATH;
                case 36:
                    return CODE_BIGINT_MATH;
                case 35:
                    return CODE;
                case 34:
                    return CHOOSE_IF;
                case 33:
                    return CHOOSE;
                case 32:
                    return CAPTURES_REDUNDANTLY;
                case 31:
                    return CAPTURES;
                case 30:
                    return CALLABLE_REDUNDANTLY;
                case 29:
                    return CALLABLE;
                case 28:
                    return BREAK_BEHAVIOUR;
                case 27:
                    return BREAK_BEHAVIOR;
                case 26:
                    return BREAKS_REDUNDANTLY;
                case 25:
                    return BREAKS;
                case 24:
                    return BIGINT_MATH;
                case 23:
                    return BIGINT;
                case 22:
                    return BEHAVIOUR;
                case 21:
                    return BEHAVIOR;
                case 20:
                    return AXIOM;
                case 19:
                    return ASSUME_REDUNDANTLY;
                case 18:
                    return ASSUME;
                case 17:
                    return ASSIGNABLE_REDUNDANTLY;
                case 16:
                    return ASSIGNABLE;
                case 15:
                    return ASSERT_REDUNDANTLY;
                case 14:
                    return JML_ASSERT;
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
        if (!text.equals(javaToken.text))
            return false;
        return true;
    }
}
