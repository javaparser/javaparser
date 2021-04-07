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
        JML_SINGLE_START(7),
        SINGLE_LINE_COMMENT(8),
        JML_MULTI_START(9),
        JML_MULTI_END(10),
        JML_SINGLE_END(11),
        INVARIANT(12),
        ABRUPT_BEHAVIOR(13),
        ABRUPT_BEHAVIOUR(14),
        MODEL_BEHAVIOR(15),
        MODEL_BEHAVIOUR(16),
        ACCESSIBLE(17),
        ACCESSIBLE_REDUNDANTLY(18),
        ALSO(19),
        ANTIVALENCE(20),
        ASSERT_REDUNDANTLY(21),
        ASSIGNABLE(22),
        ASSIGNABLE_REDUNDANTLY(23),
        ASSUME(24),
        ASSUME_REDUNDANTLY(25),
        AXIOM(26),
        BEHAVIOR(27),
        BEHAVIOUR(28),
        BIGINT(29),
        BIGINT_MATH(30),
        BREAKS(31),
        BREAKS_REDUNDANTLY(32),
        BREAK_BEHAVIOR(33),
        BREAK_BEHAVIOUR(34),
        BY(35),
        CALLABLE(36),
        CALLABLE_REDUNDANTLY(37),
        CAPTURES(38),
        CAPTURES_REDUNDANTLY(39),
        CHOOSE(40),
        CHOOSE_IF(41),
        CODE(42),
        CODE_BIGINT_MATH(43),
        CODE_JAVA_MATH(44),
        CODE_SAFE_MATH(45),
        CONSTRAINT(46),
        CONSTRAINT_REDUNDANTLY(47),
        CONSTRUCTOR(48),
        CONTINUES(49),
        CONTINUES_REDUNDANTLY(50),
        CONTINUE_BEHAVIOR(51),
        CONTINUE_BEHAVIOUR(52),
        DECLASSIFIES(53),
        DECREASES(54),
        DECREASES_REDUNDANTLY(55),
        DECREASING(56),
        DECREASING_REDUNDANTLY(57),
        DETERMINES(58),
        DIVERGES(59),
        DIVERGES_REDUNDANTLY(60),
        DURATION(61),
        DURATION_REDUNDANTLY(62),
        ELEMTYPE(63),
        ENSURES(64),
        ENSURES_REDUNDANTLY(65),
        ENSURES_FREE(66),
        REQUIRES_FREE(67),
        EQUIVALENCE(68),
        IMPLICATION(69),
        IMPLICATION_BACKWARD(70),
        ERASES(71),
        EVERYTHING(72),
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
        FRESH(85),
        GHOST(86),
        HELPER(87),
        HENCE_by(88),
        HENCE_by_REDUNDANTLY(89),
        IMPLIES_THAT(90),
        IN(91),
        INITIALIZER(92),
        INITIALLY(93),
        INSTANCE(94),
        INTO(95),
        INVARIANT_REDUNDANTLY(96),
        INVARIANT_FOR(97),
        IN_REDUNDANTLY(98),
        IS_INITIALIZED(99),
        JAVA_MATH(100),
        LBLNEG(101),
        LBLPOS(102),
        LOCKSET(103),
        LOOP_INVARIANT(104),
        LOOP_INVARIANT_REDUNDANTLY(105),
        MAINTAINING(106),
        MAINTAINING_REDUNDANTLY(107),
        MAPS(108),
        MAPS_REDUNDANTLY(109),
        MAX(110),
        MEASURED_BY(111),
        MEASURED_BY_REDUNDANTLY(112),
        METHOD(113),
        MIN(114),
        MODEL(115),
        MODEL_PROGRAM(116),
        MODIFIABLE(117),
        MODIFIABLE_REDUNDANTLY(118),
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
        NORMAL_EXAMPLE(130),
        NOTHING(131),
        NOT_ASSIGNED(132),
        NOT_MODIFIED(133),
        NOT_SPECIFIED(134),
        STRICTLY_NOTHING(135),
        NOWARN(136),
        NOWARN_OP(137),
        NULLABLE(138),
        NULLABLE_BY_DEFAULT(139),
        NUM_OF(140),
        OLD_ESC(141),
        OLD(142),
        ONLY_ACCESSED(143),
        ONLY_ASSIGNED(144),
        ONLY_CALLED(145),
        ONLY_CAPTURED(146),
        OR(147),
        POST(148),
        POST_REDUNDANTLY(149),
        PRE_ESC(150),
        PRE(151),
        PRE_REDUNDANTLY(152),
        PRODUCT(153),
        PURE(154),
        REACH(155),
        READABLE(156),
        REAL(157),
        REFINING(158),
        REPRESENTS(159),
        REPRESENTS_REDUNDANTLY(160),
        REQUIRES_REDUNDANTLY(161),
        RESULT(162),
        RETURNS(163),
        RETURNS_REDUNDANTLY(164),
        RETURN_BEHAVIOR(165),
        RETURN_BEHAVIOUR(166),
        SAFE_MATH(167),
        SAME(168),
        SET(169),
        SIGNALS(170),
        SIGNALS_ONLY(171),
        SIGNALS_ONLY_REDUNDANTLY(172),
        SIGNALS_REDUNDANTLY(173),
        SPACE_ESC(174),
        SPEC_BIGINT_MATH(175),
        SPEC_JAVA_MATH(176),
        SPEC_PACKAGE(177),
        SPEC_PRIVATE(178),
        SPEC_PROTECTED(179),
        SPEC_PUBLIC(180),
        SPEC_SAFE_MATH(181),
        STATIC_INITIALIZER(182),
        STRICTLY_PURE(183),
        SUBTYPE(184),
        SUCH_THAT(185),
        SUM(186),
        TYPE(187),
        TYPEOF(188),
        UNINITIALIZED(189),
        UNKNOWN_OP(190),
        UNKNOWN_OP_EQ(191),
        UNREACHABLE(192),
        WARN(193),
        WARN_OP(194),
        WHEN(195),
        WHEN_REDUNDANTLY(196),
        WORKING_SPACE_ESC(197),
        WORKING_SPACE(198),
        WORKING_SPACE_REDUNDANTLY(199),
        WRITABLE(200),
        LOCSET(201),
        EMPTYSET(202),
        SINGLETON(203),
        STATIC_INVARIANT_FOR(204),
        SETMINUS(205),
        ALLFIELDS(206),
        ALLOBJECTS(207),
        NEWELEMSFRESH(208),
        NEW_OBJECTS(209),
        DISJOINT(210),
        SUBSET(211),
        UNION(212),
        INFINITE_UNION(213),
        INTERSECT(214),
        ENTER_JAVADOC_COMMENT(215),
        ENTER_MULTILINE_COMMENT(216),
        JAVADOC_COMMENT(217),
        MULTI_LINE_COMMENT(218),
        COMMENT_CONTENT(219),
        ABSTRACT(220),
        ASSERT(221),
        BOOLEAN(222),
        BREAK(223),
        BYTE(224),
        CASE(225),
        CATCH(226),
        CHAR(227),
        CLASS(228),
        CONST(229),
        CONTINUE(230),
        _DEFAULT(231),
        DO(232),
        DOUBLE(233),
        ELSE(234),
        ENUM(235),
        EXTENDS(236),
        FALSE(237),
        FINAL(238),
        FINALLY(239),
        FLOAT(240),
        FOR(241),
        GOTO(242),
        IF(243),
        IMPLEMENTS(244),
        IMPORT(245),
        INSTANCEOF(246),
        INT(247),
        INTERFACE(248),
        LONG(249),
        NATIVE(250),
        NEW(251),
        NULL(252),
        PACKAGE(253),
        PRIVATE(254),
        PROTECTED(255),
        PUBLIC(256),
        RECORD(257),
        RETURN(258),
        SHORT(259),
        STATIC(260),
        STRICTFP(261),
        SUPER(262),
        SWITCH(263),
        SYNCHRONIZED(264),
        THIS(265),
        THROW(266),
        THROWS(267),
        TRANSIENT(268),
        TRUE(269),
        TRY(270),
        VOID(271),
        VOLATILE(272),
        WHILE(273),
        YIELD(274),
        REQUIRES(275),
        TO(276),
        WITH(277),
        OPEN(278),
        OPENS(279),
        USES(280),
        MODULE(281),
        EXPORTS(282),
        PROVIDES(283),
        TRANSITIVE(284),
        LONG_LITERAL(285),
        INTEGER_LITERAL(286),
        DECIMAL_LITERAL(287),
        HEX_LITERAL(288),
        OCTAL_LITERAL(289),
        BINARY_LITERAL(290),
        FLOATING_POINT_LITERAL(291),
        DECIMAL_FLOATING_POINT_LITERAL(292),
        DECIMAL_EXPONENT(293),
        HEXADECIMAL_FLOATING_POINT_LITERAL(294),
        HEXADECIMAL_EXPONENT(295),
        HEX_DIGITS(296),
        UNICODE_ESCAPE(297),
        CHARACTER_LITERAL(298),
        STRING_LITERAL(299),
        ENTER_TEXT_BLOCK(300),
        TEXT_BLOCK_LITERAL(301),
        TEXT_BLOCK_CONTENT(302),
        JML_IDENTIFIER(303),
        IDENTIFIER(304),
        LETTER(305),
        PART_LETTER(306),
        LPAREN(307),
        RPAREN(308),
        LBRACE(309),
        RBRACE(310),
        LBRACKET(311),
        RBRACKET(312),
        SEMICOLON(313),
        COMMA(314),
        DOT(315),
        ELLIPSIS(316),
        AT(317),
        DOUBLECOLON(318),
        ASSIGN(319),
        LT(320),
        BANG(321),
        TILDE(322),
        HOOK(323),
        COLON(324),
        ARROW(325),
        EQ(326),
        GE(327),
        LE(328),
        NE(329),
        SC_AND(330),
        SC_OR(331),
        INCR(332),
        DECR(333),
        PLUS(334),
        MINUS(335),
        STAR(336),
        SLASH(337),
        BIT_AND(338),
        BIT_OR(339),
        XOR(340),
        REM(341),
        LSHIFT(342),
        PLUSASSIGN(343),
        MINUSASSIGN(344),
        STARASSIGN(345),
        SLASHASSIGN(346),
        ANDASSIGN(347),
        ORASSIGN(348),
        XORASSIGN(349),
        REMASSIGN(350),
        LSHIFTASSIGN(351),
        RSIGNEDSHIFTASSIGN(352),
        RUNSIGNEDSHIFTASSIGN(353),
        RUNSIGNEDSHIFT(354),
        RSIGNEDSHIFT(355),
        GT(356),
        CTRL_Z(357);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 357:
                    return CTRL_Z;
                case 356:
                    return GT;
                case 355:
                    return RSIGNEDSHIFT;
                case 354:
                    return RUNSIGNEDSHIFT;
                case 353:
                    return RUNSIGNEDSHIFTASSIGN;
                case 352:
                    return RSIGNEDSHIFTASSIGN;
                case 351:
                    return LSHIFTASSIGN;
                case 350:
                    return REMASSIGN;
                case 349:
                    return XORASSIGN;
                case 348:
                    return ORASSIGN;
                case 347:
                    return ANDASSIGN;
                case 346:
                    return SLASHASSIGN;
                case 345:
                    return STARASSIGN;
                case 344:
                    return MINUSASSIGN;
                case 343:
                    return PLUSASSIGN;
                case 342:
                    return LSHIFT;
                case 341:
                    return REM;
                case 340:
                    return XOR;
                case 339:
                    return BIT_OR;
                case 338:
                    return BIT_AND;
                case 337:
                    return SLASH;
                case 336:
                    return STAR;
                case 335:
                    return MINUS;
                case 334:
                    return PLUS;
                case 333:
                    return DECR;
                case 332:
                    return INCR;
                case 331:
                    return SC_OR;
                case 330:
                    return SC_AND;
                case 329:
                    return NE;
                case 328:
                    return LE;
                case 327:
                    return GE;
                case 326:
                    return EQ;
                case 325:
                    return ARROW;
                case 324:
                    return COLON;
                case 323:
                    return HOOK;
                case 322:
                    return TILDE;
                case 321:
                    return BANG;
                case 320:
                    return LT;
                case 319:
                    return ASSIGN;
                case 318:
                    return DOUBLECOLON;
                case 317:
                    return AT;
                case 316:
                    return ELLIPSIS;
                case 315:
                    return DOT;
                case 314:
                    return COMMA;
                case 313:
                    return SEMICOLON;
                case 312:
                    return RBRACKET;
                case 311:
                    return LBRACKET;
                case 310:
                    return RBRACE;
                case 309:
                    return LBRACE;
                case 308:
                    return RPAREN;
                case 307:
                    return LPAREN;
                case 306:
                    return PART_LETTER;
                case 305:
                    return LETTER;
                case 304:
                    return IDENTIFIER;
                case 303:
                    return JML_IDENTIFIER;
                case 302:
                    return TEXT_BLOCK_CONTENT;
                case 301:
                    return TEXT_BLOCK_LITERAL;
                case 300:
                    return ENTER_TEXT_BLOCK;
                case 299:
                    return STRING_LITERAL;
                case 298:
                    return CHARACTER_LITERAL;
                case 297:
                    return UNICODE_ESCAPE;
                case 296:
                    return HEX_DIGITS;
                case 295:
                    return HEXADECIMAL_EXPONENT;
                case 294:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 293:
                    return DECIMAL_EXPONENT;
                case 292:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 291:
                    return FLOATING_POINT_LITERAL;
                case 290:
                    return BINARY_LITERAL;
                case 289:
                    return OCTAL_LITERAL;
                case 288:
                    return HEX_LITERAL;
                case 287:
                    return DECIMAL_LITERAL;
                case 286:
                    return INTEGER_LITERAL;
                case 285:
                    return LONG_LITERAL;
                case 284:
                    return TRANSITIVE;
                case 283:
                    return PROVIDES;
                case 282:
                    return EXPORTS;
                case 281:
                    return MODULE;
                case 280:
                    return USES;
                case 279:
                    return OPENS;
                case 278:
                    return OPEN;
                case 277:
                    return WITH;
                case 276:
                    return TO;
                case 275:
                    return REQUIRES;
                case 274:
                    return YIELD;
                case 273:
                    return WHILE;
                case 272:
                    return VOLATILE;
                case 271:
                    return VOID;
                case 270:
                    return TRY;
                case 269:
                    return TRUE;
                case 268:
                    return TRANSIENT;
                case 267:
                    return THROWS;
                case 266:
                    return THROW;
                case 265:
                    return THIS;
                case 264:
                    return SYNCHRONIZED;
                case 263:
                    return SWITCH;
                case 262:
                    return SUPER;
                case 261:
                    return STRICTFP;
                case 260:
                    return STATIC;
                case 259:
                    return SHORT;
                case 258:
                    return RETURN;
                case 257:
                    return RECORD;
                case 256:
                    return PUBLIC;
                case 255:
                    return PROTECTED;
                case 254:
                    return PRIVATE;
                case 253:
                    return PACKAGE;
                case 252:
                    return NULL;
                case 251:
                    return NEW;
                case 250:
                    return NATIVE;
                case 249:
                    return LONG;
                case 248:
                    return INTERFACE;
                case 247:
                    return INT;
                case 246:
                    return INSTANCEOF;
                case 245:
                    return IMPORT;
                case 244:
                    return IMPLEMENTS;
                case 243:
                    return IF;
                case 242:
                    return GOTO;
                case 241:
                    return FOR;
                case 240:
                    return FLOAT;
                case 239:
                    return FINALLY;
                case 238:
                    return FINAL;
                case 237:
                    return FALSE;
                case 236:
                    return EXTENDS;
                case 235:
                    return ENUM;
                case 234:
                    return ELSE;
                case 233:
                    return DOUBLE;
                case 232:
                    return DO;
                case 231:
                    return _DEFAULT;
                case 230:
                    return CONTINUE;
                case 229:
                    return CONST;
                case 228:
                    return CLASS;
                case 227:
                    return CHAR;
                case 226:
                    return CATCH;
                case 225:
                    return CASE;
                case 224:
                    return BYTE;
                case 223:
                    return BREAK;
                case 222:
                    return BOOLEAN;
                case 221:
                    return ASSERT;
                case 220:
                    return ABSTRACT;
                case 219:
                    return COMMENT_CONTENT;
                case 218:
                    return MULTI_LINE_COMMENT;
                case 217:
                    return JAVADOC_COMMENT;
                case 216:
                    return ENTER_MULTILINE_COMMENT;
                case 215:
                    return ENTER_JAVADOC_COMMENT;
                case 214:
                    return INTERSECT;
                case 213:
                    return INFINITE_UNION;
                case 212:
                    return UNION;
                case 211:
                    return SUBSET;
                case 210:
                    return DISJOINT;
                case 209:
                    return NEW_OBJECTS;
                case 208:
                    return NEWELEMSFRESH;
                case 207:
                    return ALLOBJECTS;
                case 206:
                    return ALLFIELDS;
                case 205:
                    return SETMINUS;
                case 204:
                    return STATIC_INVARIANT_FOR;
                case 203:
                    return SINGLETON;
                case 202:
                    return EMPTYSET;
                case 201:
                    return LOCSET;
                case 200:
                    return WRITABLE;
                case 199:
                    return WORKING_SPACE_REDUNDANTLY;
                case 198:
                    return WORKING_SPACE;
                case 197:
                    return WORKING_SPACE_ESC;
                case 196:
                    return WHEN_REDUNDANTLY;
                case 195:
                    return WHEN;
                case 194:
                    return WARN_OP;
                case 193:
                    return WARN;
                case 192:
                    return UNREACHABLE;
                case 191:
                    return UNKNOWN_OP_EQ;
                case 190:
                    return UNKNOWN_OP;
                case 189:
                    return UNINITIALIZED;
                case 188:
                    return TYPEOF;
                case 187:
                    return TYPE;
                case 186:
                    return SUM;
                case 185:
                    return SUCH_THAT;
                case 184:
                    return SUBTYPE;
                case 183:
                    return STRICTLY_PURE;
                case 182:
                    return STATIC_INITIALIZER;
                case 181:
                    return SPEC_SAFE_MATH;
                case 180:
                    return SPEC_PUBLIC;
                case 179:
                    return SPEC_PROTECTED;
                case 178:
                    return SPEC_PRIVATE;
                case 177:
                    return SPEC_PACKAGE;
                case 176:
                    return SPEC_JAVA_MATH;
                case 175:
                    return SPEC_BIGINT_MATH;
                case 174:
                    return SPACE_ESC;
                case 173:
                    return SIGNALS_REDUNDANTLY;
                case 172:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 171:
                    return SIGNALS_ONLY;
                case 170:
                    return SIGNALS;
                case 169:
                    return SET;
                case 168:
                    return SAME;
                case 167:
                    return SAFE_MATH;
                case 166:
                    return RETURN_BEHAVIOUR;
                case 165:
                    return RETURN_BEHAVIOR;
                case 164:
                    return RETURNS_REDUNDANTLY;
                case 163:
                    return RETURNS;
                case 162:
                    return RESULT;
                case 161:
                    return REQUIRES_REDUNDANTLY;
                case 160:
                    return REPRESENTS_REDUNDANTLY;
                case 159:
                    return REPRESENTS;
                case 158:
                    return REFINING;
                case 157:
                    return REAL;
                case 156:
                    return READABLE;
                case 155:
                    return REACH;
                case 154:
                    return PURE;
                case 153:
                    return PRODUCT;
                case 152:
                    return PRE_REDUNDANTLY;
                case 151:
                    return PRE;
                case 150:
                    return PRE_ESC;
                case 149:
                    return POST_REDUNDANTLY;
                case 148:
                    return POST;
                case 147:
                    return OR;
                case 146:
                    return ONLY_CAPTURED;
                case 145:
                    return ONLY_CALLED;
                case 144:
                    return ONLY_ASSIGNED;
                case 143:
                    return ONLY_ACCESSED;
                case 142:
                    return OLD;
                case 141:
                    return OLD_ESC;
                case 140:
                    return NUM_OF;
                case 139:
                    return NULLABLE_BY_DEFAULT;
                case 138:
                    return NULLABLE;
                case 137:
                    return NOWARN_OP;
                case 136:
                    return NOWARN;
                case 135:
                    return STRICTLY_NOTHING;
                case 134:
                    return NOT_SPECIFIED;
                case 133:
                    return NOT_MODIFIED;
                case 132:
                    return NOT_ASSIGNED;
                case 131:
                    return NOTHING;
                case 130:
                    return NORMAL_EXAMPLE;
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
                    return MODIFIABLE_REDUNDANTLY;
                case 117:
                    return MODIFIABLE;
                case 116:
                    return MODEL_PROGRAM;
                case 115:
                    return MODEL;
                case 114:
                    return MIN;
                case 113:
                    return METHOD;
                case 112:
                    return MEASURED_BY_REDUNDANTLY;
                case 111:
                    return MEASURED_BY;
                case 110:
                    return MAX;
                case 109:
                    return MAPS_REDUNDANTLY;
                case 108:
                    return MAPS;
                case 107:
                    return MAINTAINING_REDUNDANTLY;
                case 106:
                    return MAINTAINING;
                case 105:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 104:
                    return LOOP_INVARIANT;
                case 103:
                    return LOCKSET;
                case 102:
                    return LBLPOS;
                case 101:
                    return LBLNEG;
                case 100:
                    return JAVA_MATH;
                case 99:
                    return IS_INITIALIZED;
                case 98:
                    return IN_REDUNDANTLY;
                case 97:
                    return INVARIANT_FOR;
                case 96:
                    return INVARIANT_REDUNDANTLY;
                case 95:
                    return INTO;
                case 94:
                    return INSTANCE;
                case 93:
                    return INITIALLY;
                case 92:
                    return INITIALIZER;
                case 91:
                    return IN;
                case 90:
                    return IMPLIES_THAT;
                case 89:
                    return HENCE_by_REDUNDANTLY;
                case 88:
                    return HENCE_by;
                case 87:
                    return HELPER;
                case 86:
                    return GHOST;
                case 85:
                    return FRESH;
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
                    return EVERYTHING;
                case 71:
                    return ERASES;
                case 70:
                    return IMPLICATION_BACKWARD;
                case 69:
                    return IMPLICATION;
                case 68:
                    return EQUIVALENCE;
                case 67:
                    return REQUIRES_FREE;
                case 66:
                    return ENSURES_FREE;
                case 65:
                    return ENSURES_REDUNDANTLY;
                case 64:
                    return ENSURES;
                case 63:
                    return ELEMTYPE;
                case 62:
                    return DURATION_REDUNDANTLY;
                case 61:
                    return DURATION;
                case 60:
                    return DIVERGES_REDUNDANTLY;
                case 59:
                    return DIVERGES;
                case 58:
                    return DETERMINES;
                case 57:
                    return DECREASING_REDUNDANTLY;
                case 56:
                    return DECREASING;
                case 55:
                    return DECREASES_REDUNDANTLY;
                case 54:
                    return DECREASES;
                case 53:
                    return DECLASSIFIES;
                case 52:
                    return CONTINUE_BEHAVIOUR;
                case 51:
                    return CONTINUE_BEHAVIOR;
                case 50:
                    return CONTINUES_REDUNDANTLY;
                case 49:
                    return CONTINUES;
                case 48:
                    return CONSTRUCTOR;
                case 47:
                    return CONSTRAINT_REDUNDANTLY;
                case 46:
                    return CONSTRAINT;
                case 45:
                    return CODE_SAFE_MATH;
                case 44:
                    return CODE_JAVA_MATH;
                case 43:
                    return CODE_BIGINT_MATH;
                case 42:
                    return CODE;
                case 41:
                    return CHOOSE_IF;
                case 40:
                    return CHOOSE;
                case 39:
                    return CAPTURES_REDUNDANTLY;
                case 38:
                    return CAPTURES;
                case 37:
                    return CALLABLE_REDUNDANTLY;
                case 36:
                    return CALLABLE;
                case 35:
                    return BY;
                case 34:
                    return BREAK_BEHAVIOUR;
                case 33:
                    return BREAK_BEHAVIOR;
                case 32:
                    return BREAKS_REDUNDANTLY;
                case 31:
                    return BREAKS;
                case 30:
                    return BIGINT_MATH;
                case 29:
                    return BIGINT;
                case 28:
                    return BEHAVIOUR;
                case 27:
                    return BEHAVIOR;
                case 26:
                    return AXIOM;
                case 25:
                    return ASSUME_REDUNDANTLY;
                case 24:
                    return ASSUME;
                case 23:
                    return ASSIGNABLE_REDUNDANTLY;
                case 22:
                    return ASSIGNABLE;
                case 21:
                    return ASSERT_REDUNDANTLY;
                case 20:
                    return ANTIVALENCE;
                case 19:
                    return ALSO;
                case 18:
                    return ACCESSIBLE_REDUNDANTLY;
                case 17:
                    return ACCESSIBLE;
                case 16:
                    return MODEL_BEHAVIOUR;
                case 15:
                    return MODEL_BEHAVIOR;
                case 14:
                    return ABRUPT_BEHAVIOUR;
                case 13:
                    return ABRUPT_BEHAVIOR;
                case 12:
                    return INVARIANT;
                case 11:
                    return JML_SINGLE_END;
                case 10:
                    return JML_MULTI_END;
                case 9:
                    return JML_MULTI_START;
                case 8:
                    return SINGLE_LINE_COMMENT;
                case 7:
                    return JML_SINGLE_START;
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
        if (!text.equals(javaToken.text))
            return false;
        return true;
    }
}
