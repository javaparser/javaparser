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
        INTO(97),
        INVARIANT_REDUNDANTLY(98),
        INVARIANT_FOR(99),
        IN_REDUNDANTLY(100),
        IS_INITIALIZED(101),
        JAVA_MATH(102),
        LBLNEG(103),
        LBLPOS(104),
        LOCKSET(105),
        LOOP_INVARIANT(106),
        LOOP_INVARIANT_REDUNDANTLY(107),
        MAINTAINING(108),
        MAINTAINING_REDUNDANTLY(109),
        MAPS(110),
        MAPS_REDUNDANTLY(111),
        MAX(112),
        MEASURED_BY(113),
        MEASURED_BY_REDUNDANTLY(114),
        METHOD(115),
        MIN(116),
        MODEL(117),
        MODEL_PROGRAM(118),
        MODIFIABLE(119),
        MODIFIABLE_REDUNDANTLY(120),
        MODIFIES(121),
        MODIFIES_REDUNDANTLY(122),
        MONITORED(123),
        MONITORS_FOR(124),
        NESTED_CONTRACT_END(125),
        NESTED_CONTRACT_START(126),
        NEW_OBJECT(127),
        NONNULLELEMENTS(128),
        NON_NULL(129),
        NORMAL_BEHAVIOR(130),
        NORMAL_BEHAVIOUR(131),
        NORMAL_EXAMPLE(132),
        NOTHING(133),
        NOT_ASSIGNED(134),
        NOT_MODIFIED(135),
        NOT_SPECIFIED(136),
        STRICTLY_NOTHING(137),
        NOWARN(138),
        NOWARN_OP(139),
        NULLABLE(140),
        NULLABLE_BY_DEFAULT(141),
        NUM_OF(142),
        OLD_ESC(143),
        OLD(144),
        ONLY_ACCESSED(145),
        ONLY_ASSIGNED(146),
        ONLY_CALLED(147),
        ONLY_CAPTURED(148),
        OR(149),
        POST(150),
        POST_REDUNDANTLY(151),
        PRE_ESC(152),
        PRE(153),
        PRE_REDUNDANTLY(154),
        PRODUCT(155),
        PURE(156),
        REACH(157),
        READABLE(158),
        REAL(159),
        REFINING(160),
        REPRESENTS(161),
        REPRESENTS_REDUNDANTLY(162),
        REQUIRES_REDUNDANTLY(163),
        RESULT(164),
        RETURNS(165),
        RETURNS_REDUNDANTLY(166),
        RETURN_BEHAVIOR(167),
        RETURN_BEHAVIOUR(168),
        SAFE_MATH(169),
        SAME(170),
        SET(171),
        SIGNALS(172),
        SIGNALS_ONLY(173),
        SIGNALS_ONLY_REDUNDANTLY(174),
        SIGNALS_REDUNDANTLY(175),
        SPACE_ESC(176),
        SPEC_BIGINT_MATH(177),
        SPEC_JAVA_MATH(178),
        SPEC_PACKAGE(179),
        SPEC_PRIVATE(180),
        SPEC_PROTECTED(181),
        SPEC_PUBLIC(182),
        SPEC_SAFE_MATH(183),
        STATIC_INITIALIZER(184),
        STRICTLY_PURE(185),
        SUBTYPE(186),
        SUCH_THAT(187),
        SUM(188),
        TYPE(189),
        TYPEOF(190),
        UNINITIALIZED(191),
        UNKNOWN_OP(192),
        UNKNOWN_OP_EQ(193),
        UNREACHABLE(194),
        WARN(195),
        WARN_OP(196),
        WHEN(197),
        WHEN_REDUNDANTLY(198),
        WORKING_SPACE_ESC(199),
        WORKING_SPACE(200),
        WORKING_SPACE_REDUNDANTLY(201),
        WRITABLE(202),
        LOCSET(203),
        STOREREF(204),
        EMPTYSET(205),
        SINGLETON(206),
        STATIC_INVARIANT_FOR(207),
        SETMINUS(208),
        ALLFIELDS(209),
        ALLOBJECTS(210),
        NEWELEMSFRESH(211),
        NEW_OBJECTS(212),
        DISJOINT(213),
        SUBSET(214),
        UNION(215),
        INFINITE_UNION(216),
        INTERSECT(217),
        ENTER_JAVADOC_COMMENT(218),
        ENTER_MULTILINE_COMMENT(219),
        JAVADOC_COMMENT(220),
        MULTI_LINE_COMMENT(221),
        COMMENT_CONTENT(222),
        ABSTRACT(223),
        ASSERT(224),
        BOOLEAN(225),
        BREAK(226),
        BYTE(227),
        CASE(228),
        CATCH(229),
        CHAR(230),
        CLASS(231),
        CONST(232),
        CONTINUE(233),
        _DEFAULT(234),
        DO(235),
        DOUBLE(236),
        ELSE(237),
        ENUM(238),
        EXTENDS(239),
        FALSE(240),
        FINAL(241),
        FINALLY(242),
        FLOAT(243),
        FOR(244),
        GOTO(245),
        IF(246),
        IMPLEMENTS(247),
        IMPORT(248),
        INSTANCEOF(249),
        INT(250),
        INTERFACE(251),
        LONG(252),
        NATIVE(253),
        NEW(254),
        NULL(255),
        PACKAGE(256),
        PRIVATE(257),
        PROTECTED(258),
        PUBLIC(259),
        RECORD(260),
        RETURN(261),
        SHORT(262),
        STATIC(263),
        STRICTFP(264),
        SUPER(265),
        SWITCH(266),
        SYNCHRONIZED(267),
        THIS(268),
        THROW(269),
        THROWS(270),
        TRANSIENT(271),
        TRUE(272),
        TRY(273),
        VOID(274),
        VOLATILE(275),
        WHILE(276),
        YIELD(277),
        REQUIRES(278),
        TO(279),
        WITH(280),
        OPEN(281),
        OPENS(282),
        USES(283),
        MODULE(284),
        EXPORTS(285),
        PROVIDES(286),
        TRANSITIVE(287),
        LONG_LITERAL(288),
        INTEGER_LITERAL(289),
        DECIMAL_LITERAL(290),
        HEX_LITERAL(291),
        OCTAL_LITERAL(292),
        BINARY_LITERAL(293),
        FLOATING_POINT_LITERAL(294),
        DECIMAL_FLOATING_POINT_LITERAL(295),
        DECIMAL_EXPONENT(296),
        HEXADECIMAL_FLOATING_POINT_LITERAL(297),
        HEXADECIMAL_EXPONENT(298),
        HEX_DIGITS(299),
        UNICODE_ESCAPE(300),
        CHARACTER_LITERAL(301),
        STRING_LITERAL(302),
        ENTER_TEXT_BLOCK(303),
        TEXT_BLOCK_LITERAL(304),
        TEXT_BLOCK_CONTENT(305),
        JML_IDENTIFIER(306),
        IDENTIFIER(307),
        LETTER(308),
        PART_LETTER(309),
        LPAREN(310),
        RPAREN(311),
        LBRACE(312),
        RBRACE(313),
        LBRACKET(314),
        RBRACKET(315),
        SEMICOLON(316),
        COMMA(317),
        DOT(318),
        ELLIPSIS(319),
        AT(320),
        DOUBLECOLON(321),
        ASSIGN(322),
        LT(323),
        BANG(324),
        TILDE(325),
        HOOK(326),
        COLON(327),
        ARROW(328),
        EQ(329),
        GE(330),
        LE(331),
        NE(332),
        SC_AND(333),
        SC_OR(334),
        INCR(335),
        DECR(336),
        PLUS(337),
        MINUS(338),
        STAR(339),
        SLASH(340),
        BIT_AND(341),
        BIT_OR(342),
        XOR(343),
        REM(344),
        LSHIFT(345),
        PLUSASSIGN(346),
        MINUSASSIGN(347),
        STARASSIGN(348),
        SLASHASSIGN(349),
        ANDASSIGN(350),
        ORASSIGN(351),
        XORASSIGN(352),
        REMASSIGN(353),
        LSHIFTASSIGN(354),
        RSIGNEDSHIFTASSIGN(355),
        RUNSIGNEDSHIFTASSIGN(356),
        RUNSIGNEDSHIFT(357),
        RSIGNEDSHIFT(358),
        GT(359),
        CTRL_Z(360);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 360:
                    return CTRL_Z;
                case 359:
                    return GT;
                case 358:
                    return RSIGNEDSHIFT;
                case 357:
                    return RUNSIGNEDSHIFT;
                case 356:
                    return RUNSIGNEDSHIFTASSIGN;
                case 355:
                    return RSIGNEDSHIFTASSIGN;
                case 354:
                    return LSHIFTASSIGN;
                case 353:
                    return REMASSIGN;
                case 352:
                    return XORASSIGN;
                case 351:
                    return ORASSIGN;
                case 350:
                    return ANDASSIGN;
                case 349:
                    return SLASHASSIGN;
                case 348:
                    return STARASSIGN;
                case 347:
                    return MINUSASSIGN;
                case 346:
                    return PLUSASSIGN;
                case 345:
                    return LSHIFT;
                case 344:
                    return REM;
                case 343:
                    return XOR;
                case 342:
                    return BIT_OR;
                case 341:
                    return BIT_AND;
                case 340:
                    return SLASH;
                case 339:
                    return STAR;
                case 338:
                    return MINUS;
                case 337:
                    return PLUS;
                case 336:
                    return DECR;
                case 335:
                    return INCR;
                case 334:
                    return SC_OR;
                case 333:
                    return SC_AND;
                case 332:
                    return NE;
                case 331:
                    return LE;
                case 330:
                    return GE;
                case 329:
                    return EQ;
                case 328:
                    return ARROW;
                case 327:
                    return COLON;
                case 326:
                    return HOOK;
                case 325:
                    return TILDE;
                case 324:
                    return BANG;
                case 323:
                    return LT;
                case 322:
                    return ASSIGN;
                case 321:
                    return DOUBLECOLON;
                case 320:
                    return AT;
                case 319:
                    return ELLIPSIS;
                case 318:
                    return DOT;
                case 317:
                    return COMMA;
                case 316:
                    return SEMICOLON;
                case 315:
                    return RBRACKET;
                case 314:
                    return LBRACKET;
                case 313:
                    return RBRACE;
                case 312:
                    return LBRACE;
                case 311:
                    return RPAREN;
                case 310:
                    return LPAREN;
                case 309:
                    return PART_LETTER;
                case 308:
                    return LETTER;
                case 307:
                    return IDENTIFIER;
                case 306:
                    return JML_IDENTIFIER;
                case 305:
                    return TEXT_BLOCK_CONTENT;
                case 304:
                    return TEXT_BLOCK_LITERAL;
                case 303:
                    return ENTER_TEXT_BLOCK;
                case 302:
                    return STRING_LITERAL;
                case 301:
                    return CHARACTER_LITERAL;
                case 300:
                    return UNICODE_ESCAPE;
                case 299:
                    return HEX_DIGITS;
                case 298:
                    return HEXADECIMAL_EXPONENT;
                case 297:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 296:
                    return DECIMAL_EXPONENT;
                case 295:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 294:
                    return FLOATING_POINT_LITERAL;
                case 293:
                    return BINARY_LITERAL;
                case 292:
                    return OCTAL_LITERAL;
                case 291:
                    return HEX_LITERAL;
                case 290:
                    return DECIMAL_LITERAL;
                case 289:
                    return INTEGER_LITERAL;
                case 288:
                    return LONG_LITERAL;
                case 287:
                    return TRANSITIVE;
                case 286:
                    return PROVIDES;
                case 285:
                    return EXPORTS;
                case 284:
                    return MODULE;
                case 283:
                    return USES;
                case 282:
                    return OPENS;
                case 281:
                    return OPEN;
                case 280:
                    return WITH;
                case 279:
                    return TO;
                case 278:
                    return REQUIRES;
                case 277:
                    return YIELD;
                case 276:
                    return WHILE;
                case 275:
                    return VOLATILE;
                case 274:
                    return VOID;
                case 273:
                    return TRY;
                case 272:
                    return TRUE;
                case 271:
                    return TRANSIENT;
                case 270:
                    return THROWS;
                case 269:
                    return THROW;
                case 268:
                    return THIS;
                case 267:
                    return SYNCHRONIZED;
                case 266:
                    return SWITCH;
                case 265:
                    return SUPER;
                case 264:
                    return STRICTFP;
                case 263:
                    return STATIC;
                case 262:
                    return SHORT;
                case 261:
                    return RETURN;
                case 260:
                    return RECORD;
                case 259:
                    return PUBLIC;
                case 258:
                    return PROTECTED;
                case 257:
                    return PRIVATE;
                case 256:
                    return PACKAGE;
                case 255:
                    return NULL;
                case 254:
                    return NEW;
                case 253:
                    return NATIVE;
                case 252:
                    return LONG;
                case 251:
                    return INTERFACE;
                case 250:
                    return INT;
                case 249:
                    return INSTANCEOF;
                case 248:
                    return IMPORT;
                case 247:
                    return IMPLEMENTS;
                case 246:
                    return IF;
                case 245:
                    return GOTO;
                case 244:
                    return FOR;
                case 243:
                    return FLOAT;
                case 242:
                    return FINALLY;
                case 241:
                    return FINAL;
                case 240:
                    return FALSE;
                case 239:
                    return EXTENDS;
                case 238:
                    return ENUM;
                case 237:
                    return ELSE;
                case 236:
                    return DOUBLE;
                case 235:
                    return DO;
                case 234:
                    return _DEFAULT;
                case 233:
                    return CONTINUE;
                case 232:
                    return CONST;
                case 231:
                    return CLASS;
                case 230:
                    return CHAR;
                case 229:
                    return CATCH;
                case 228:
                    return CASE;
                case 227:
                    return BYTE;
                case 226:
                    return BREAK;
                case 225:
                    return BOOLEAN;
                case 224:
                    return ASSERT;
                case 223:
                    return ABSTRACT;
                case 222:
                    return COMMENT_CONTENT;
                case 221:
                    return MULTI_LINE_COMMENT;
                case 220:
                    return JAVADOC_COMMENT;
                case 219:
                    return ENTER_MULTILINE_COMMENT;
                case 218:
                    return ENTER_JAVADOC_COMMENT;
                case 217:
                    return INTERSECT;
                case 216:
                    return INFINITE_UNION;
                case 215:
                    return UNION;
                case 214:
                    return SUBSET;
                case 213:
                    return DISJOINT;
                case 212:
                    return NEW_OBJECTS;
                case 211:
                    return NEWELEMSFRESH;
                case 210:
                    return ALLOBJECTS;
                case 209:
                    return ALLFIELDS;
                case 208:
                    return SETMINUS;
                case 207:
                    return STATIC_INVARIANT_FOR;
                case 206:
                    return SINGLETON;
                case 205:
                    return EMPTYSET;
                case 204:
                    return STOREREF;
                case 203:
                    return LOCSET;
                case 202:
                    return WRITABLE;
                case 201:
                    return WORKING_SPACE_REDUNDANTLY;
                case 200:
                    return WORKING_SPACE;
                case 199:
                    return WORKING_SPACE_ESC;
                case 198:
                    return WHEN_REDUNDANTLY;
                case 197:
                    return WHEN;
                case 196:
                    return WARN_OP;
                case 195:
                    return WARN;
                case 194:
                    return UNREACHABLE;
                case 193:
                    return UNKNOWN_OP_EQ;
                case 192:
                    return UNKNOWN_OP;
                case 191:
                    return UNINITIALIZED;
                case 190:
                    return TYPEOF;
                case 189:
                    return TYPE;
                case 188:
                    return SUM;
                case 187:
                    return SUCH_THAT;
                case 186:
                    return SUBTYPE;
                case 185:
                    return STRICTLY_PURE;
                case 184:
                    return STATIC_INITIALIZER;
                case 183:
                    return SPEC_SAFE_MATH;
                case 182:
                    return SPEC_PUBLIC;
                case 181:
                    return SPEC_PROTECTED;
                case 180:
                    return SPEC_PRIVATE;
                case 179:
                    return SPEC_PACKAGE;
                case 178:
                    return SPEC_JAVA_MATH;
                case 177:
                    return SPEC_BIGINT_MATH;
                case 176:
                    return SPACE_ESC;
                case 175:
                    return SIGNALS_REDUNDANTLY;
                case 174:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 173:
                    return SIGNALS_ONLY;
                case 172:
                    return SIGNALS;
                case 171:
                    return SET;
                case 170:
                    return SAME;
                case 169:
                    return SAFE_MATH;
                case 168:
                    return RETURN_BEHAVIOUR;
                case 167:
                    return RETURN_BEHAVIOR;
                case 166:
                    return RETURNS_REDUNDANTLY;
                case 165:
                    return RETURNS;
                case 164:
                    return RESULT;
                case 163:
                    return REQUIRES_REDUNDANTLY;
                case 162:
                    return REPRESENTS_REDUNDANTLY;
                case 161:
                    return REPRESENTS;
                case 160:
                    return REFINING;
                case 159:
                    return REAL;
                case 158:
                    return READABLE;
                case 157:
                    return REACH;
                case 156:
                    return PURE;
                case 155:
                    return PRODUCT;
                case 154:
                    return PRE_REDUNDANTLY;
                case 153:
                    return PRE;
                case 152:
                    return PRE_ESC;
                case 151:
                    return POST_REDUNDANTLY;
                case 150:
                    return POST;
                case 149:
                    return OR;
                case 148:
                    return ONLY_CAPTURED;
                case 147:
                    return ONLY_CALLED;
                case 146:
                    return ONLY_ASSIGNED;
                case 145:
                    return ONLY_ACCESSED;
                case 144:
                    return OLD;
                case 143:
                    return OLD_ESC;
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
                    return STRICTLY_NOTHING;
                case 136:
                    return NOT_SPECIFIED;
                case 135:
                    return NOT_MODIFIED;
                case 134:
                    return NOT_ASSIGNED;
                case 133:
                    return NOTHING;
                case 132:
                    return NORMAL_EXAMPLE;
                case 131:
                    return NORMAL_BEHAVIOUR;
                case 130:
                    return NORMAL_BEHAVIOR;
                case 129:
                    return NON_NULL;
                case 128:
                    return NONNULLELEMENTS;
                case 127:
                    return NEW_OBJECT;
                case 126:
                    return NESTED_CONTRACT_START;
                case 125:
                    return NESTED_CONTRACT_END;
                case 124:
                    return MONITORS_FOR;
                case 123:
                    return MONITORED;
                case 122:
                    return MODIFIES_REDUNDANTLY;
                case 121:
                    return MODIFIES;
                case 120:
                    return MODIFIABLE_REDUNDANTLY;
                case 119:
                    return MODIFIABLE;
                case 118:
                    return MODEL_PROGRAM;
                case 117:
                    return MODEL;
                case 116:
                    return MIN;
                case 115:
                    return METHOD;
                case 114:
                    return MEASURED_BY_REDUNDANTLY;
                case 113:
                    return MEASURED_BY;
                case 112:
                    return MAX;
                case 111:
                    return MAPS_REDUNDANTLY;
                case 110:
                    return MAPS;
                case 109:
                    return MAINTAINING_REDUNDANTLY;
                case 108:
                    return MAINTAINING;
                case 107:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 106:
                    return LOOP_INVARIANT;
                case 105:
                    return LOCKSET;
                case 104:
                    return LBLPOS;
                case 103:
                    return LBLNEG;
                case 102:
                    return JAVA_MATH;
                case 101:
                    return IS_INITIALIZED;
                case 100:
                    return IN_REDUNDANTLY;
                case 99:
                    return INVARIANT_FOR;
                case 98:
                    return INVARIANT_REDUNDANTLY;
                case 97:
                    return INTO;
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
