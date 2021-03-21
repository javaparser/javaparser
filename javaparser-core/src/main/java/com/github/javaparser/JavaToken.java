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
        ABRUPT_BEHAVIOR(13),
        ABRUPT_BEHAVIOUR(14),
        ACCESSIBLE(15),
        ACCESSIBLE_REDUNDANTLY(16),
        ALSO(17),
        ANTIVALENCE(18),
        ASSERT_REDUNDANTLY(19),
        ASSIGNABLE(20),
        ASSIGNABLE_REDUNDANTLY(21),
        ASSUME(22),
        ASSUME_REDUNDANTLY(23),
        AXIOM(24),
        BEHAVIOR(25),
        BEHAVIOUR(26),
        BIGINT(27),
        BIGINT_MATH(28),
        BREAKS(29),
        BREAKS_REDUNDANTLY(30),
        BREAK_BEHAVIOR(31),
        BY(32),
        CALLABLE(33),
        CALLABLE_REDUNDANTLY(34),
        CAPTURES(35),
        CAPTURES_REDUNDANTLY(36),
        CHOOSE(37),
        CHOOSE_IF(38),
        CODE(39),
        CODE_BIGINT_MATH(40),
        CODE_JAVA_MATH(41),
        CODE_SAFE_MATH(42),
        CONSTRAINT(43),
        CONSTRAINT_REDUNDANTLY(44),
        CONSTRUCTOR(45),
        CONTINUES(46),
        CONTINUES_REDUNDANTLY(47),
        CONTINUE_BEHAVIOR(48),
        DECLASSIFIES(49),
        DECREASES(50),
        DECREASES_REDUNDANTLY(51),
        DECREASING(52),
        DECREASING_REDUNDANTLY(53),
        DETERMINES(54),
        DIVERGES(55),
        DIVERGES_REDUNDANTLY(56),
        DURATION(57),
        DURATION_REDUNDANTLY(58),
        ELEMTYPE(59),
        ENSURES(60),
        ENSURES_REDUNDANTLY(61),
        ENSURES_FREE(62),
        REQUIRES_FREE(63),
        EQUIVALENCE(64),
        ERASES(65),
        EVERYTHING(66),
        EXAMPLE(67),
        EXCEPTIONAL_BEHAVIOR(68),
        EXCEPTIONAL_BEHAVIOUR(69),
        EXCEPTIONAL_EXAMPLE(70),
        EXISTS(71),
        EXSURES(72),
        EXSURES_REDUNDANTLY(73),
        EXTRACT(74),
        FIELD(75),
        FORALLQ(76),
        FORALL(77),
        FOR_EXAMPLE(78),
        FRESH(79),
        GHOST(80),
        HELPER(81),
        HENCE_by(82),
        HENCE_by_REDUNDANTLY(83),
        IMPLIES_THAT(84),
        IN(85),
        INITIALIZER(86),
        INITIALLY(87),
        INSTANCE(88),
        INTO(89),
        INVARIANT_REDUNDANTLY(90),
        INVARIANT_fOR(91),
        IN_redundantly(92),
        IS_INITIALIZED(93),
        JAVA_MATH(94),
        LBLNEG(95),
        LBLPOS(96),
        LOCKSET(97),
        LOOP_INVARIANT(98),
        LOOP_INVARIANT_REDUNDANTLY(99),
        MAINTAINING(100),
        MAINTAINING_REDUNDANTLY(101),
        MAPS(102),
        MAPS_REDUNDANTLY(103),
        MAX(104),
        MEASURED_BY(105),
        MEASURED_BY_REDUNDANTLY(106),
        METHOD(107),
        MIN(108),
        MODEL(109),
        MODEL_PROGRAM(110),
        MODIFIABLE(111),
        MODIFIABLE_redundantly(112),
        MODIFIES(113),
        MODIFIES_redundantly(114),
        MONITORED(115),
        MONITORS_FOR(116),
        NESTED_CONTRACT_END(117),
        NESTED_CONTRACT_START(118),
        NEW_OBJECT(119),
        NONNULLELEMENTS(120),
        NON_NULL(121),
        NORMAL_BEHAVIOR(122),
        NORMAL_BEHAVIOUR(123),
        NORMAL_EXAMPLE(124),
        NOTHING(125),
        NOT_ASSIGNED(126),
        NOT_MODIFIED(127),
        NOT_SPECIFIED(128),
        STRICTLY_NOTHING(129),
        NOWARN(130),
        NOWARN_OP(131),
        NULLABLE(132),
        NULLABLE_BY_DEFAULT(133),
        NUM_OF(134),
        OLD_ESC(135),
        OLD(136),
        ONLY_ACCESSED(137),
        ONLY_ASSIGNED(138),
        ONLY_CALLED(139),
        ONLY_CAPTURED(140),
        OR(141),
        POST(142),
        POST_REDUNDANTLY(143),
        PRE_ESC(144),
        PRE(145),
        PRE_REDUNDANTLY(146),
        PRODUCT(147),
        PURE(148),
        REACH(149),
        READABLE(150),
        REAL(151),
        REFINING(152),
        REPRESENTS(153),
        REPRESENTS_REDUNDANTLY(154),
        REQUIRES_REDUNDANTLY(155),
        RESULT(156),
        RETURNS(157),
        RETURNS_REDUNDANTLY(158),
        RETURN_BEHAVIOR(159),
        RETURN_BEHAVIOUR(160),
        SAFE_MATH(161),
        SAME(162),
        SET(163),
        SIGNALS(164),
        SIGNALS_ONLY(165),
        SIGNALS_ONLY_REDUNDANTLY(166),
        SIGNALS_REDUNDANTLY(167),
        SPACE_ESC(168),
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
        TYPEOF(182),
        UNINITIALIZED(183),
        UNKNOWN_OP(184),
        UNKNOWN_OP_EQ(185),
        UNREACHABLE(186),
        WARN(187),
        WARN_OP(188),
        WHEN(189),
        WHEN_REDUNDANTLY(190),
        WORKING_SPACE_ESC(191),
        WORKING_SPACE(192),
        WORKING_SPACE_REDUNDANTLY(193),
        WRITABLE(194),
        LOCSET(195),
        EMPTYSET(196),
        SINGLETON(197),
        STATIC_INVARIANT_FOR(198),
        SETMINUS(199),
        ALLFIELDS(200),
        ALLOBJECTS(201),
        NEWELEMSFRESH(202),
        NEW_OBJECTS(203),
        DISJOINT(204),
        SUBSET(205),
        UNION(206),
        INFINITE_UNION(207),
        INTERSECT(208),
        ENTER_JAVADOC_COMMENT(209),
        ENTER_MULTILINE_COMMENT(210),
        JAVADOC_COMMENT(211),
        MULTI_LINE_COMMENT(212),
        COMMENT_CONTENT(213),
        ABSTRACT(214),
        ASSERT(215),
        BOOLEAN(216),
        BREAK(217),
        BYTE(218),
        CASE(219),
        CATCH(220),
        CHAR(221),
        CLASS(222),
        CONST(223),
        CONTINUE(224),
        _DEFAULT(225),
        DO(226),
        DOUBLE(227),
        ELSE(228),
        ENUM(229),
        EXTENDS(230),
        FALSE(231),
        FINAL(232),
        FINALLY(233),
        FLOAT(234),
        FOR(235),
        GOTO(236),
        IF(237),
        IMPLEMENTS(238),
        IMPORT(239),
        INSTANCEOF(240),
        INT(241),
        INTERFACE(242),
        LONG(243),
        NATIVE(244),
        NEW(245),
        NULL(246),
        PACKAGE(247),
        PRIVATE(248),
        PROTECTED(249),
        PUBLIC(250),
        RETURN(251),
        SHORT(252),
        STATIC(253),
        STRICTFP(254),
        SUPER(255),
        SWITCH(256),
        SYNCHRONIZED(257),
        THIS(258),
        THROW(259),
        THROWS(260),
        TRANSIENT(261),
        TRUE(262),
        TRY(263),
        VOID(264),
        VOLATILE(265),
        WHILE(266),
        YIELD(267),
        REQUIRES(268),
        TO(269),
        WITH(270),
        OPEN(271),
        OPENS(272),
        USES(273),
        MODULE(274),
        EXPORTS(275),
        PROVIDES(276),
        TRANSITIVE(277),
        LONG_LITERAL(278),
        INTEGER_LITERAL(279),
        DECIMAL_LITERAL(280),
        HEX_LITERAL(281),
        OCTAL_LITERAL(282),
        BINARY_LITERAL(283),
        FLOATING_POINT_LITERAL(284),
        DECIMAL_FLOATING_POINT_LITERAL(285),
        DECIMAL_EXPONENT(286),
        HEXADECIMAL_FLOATING_POINT_LITERAL(287),
        HEXADECIMAL_EXPONENT(288),
        HEX_DIGITS(289),
        UNICODE_ESCAPE(290),
        CHARACTER_LITERAL(291),
        STRING_LITERAL(292),
        ENTER_TEXT_BLOCK(293),
        TEXT_BLOCK_LITERAL(294),
        TEXT_BLOCK_CONTENT(295),
        JML_IDENTIFIER(296),
        IDENTIFIER(297),
        LETTER(298),
        PART_LETTER(299),
        LPAREN(300),
        RPAREN(301),
        LBRACE(302),
        RBRACE(303),
        LBRACKET(304),
        RBRACKET(305),
        SEMICOLON(306),
        COMMA(307),
        DOT(308),
        AT(309),
        ASSIGN(310),
        LT(311),
        BANG(312),
        TILDE(313),
        HOOK(314),
        COLON(315),
        ARROW(316),
        EQ(317),
        GE(318),
        LE(319),
        NE(320),
        SC_AND(321),
        SC_OR(322),
        INCR(323),
        DECR(324),
        PLUS(325),
        MINUS(326),
        STAR(327),
        SLASH(328),
        BIT_AND(329),
        BIT_OR(330),
        XOR(331),
        REM(332),
        LSHIFT(333),
        PLUSASSIGN(334),
        MINUSASSIGN(335),
        STARASSIGN(336),
        SLASHASSIGN(337),
        ANDASSIGN(338),
        ORASSIGN(339),
        XORASSIGN(340),
        REMASSIGN(341),
        LSHIFTASSIGN(342),
        RSIGNEDSHIFTASSIGN(343),
        RUNSIGNEDSHIFTASSIGN(344),
        ELLIPSIS(345),
        DOUBLECOLON(346),
        RUNSIGNEDSHIFT(347),
        RSIGNEDSHIFT(348),
        GT(349),
        CTRL_Z(350);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 350:
                    return CTRL_Z;
                case 349:
                    return GT;
                case 348:
                    return RSIGNEDSHIFT;
                case 347:
                    return RUNSIGNEDSHIFT;
                case 346:
                    return DOUBLECOLON;
                case 345:
                    return ELLIPSIS;
                case 344:
                    return RUNSIGNEDSHIFTASSIGN;
                case 343:
                    return RSIGNEDSHIFTASSIGN;
                case 342:
                    return LSHIFTASSIGN;
                case 341:
                    return REMASSIGN;
                case 340:
                    return XORASSIGN;
                case 339:
                    return ORASSIGN;
                case 338:
                    return ANDASSIGN;
                case 337:
                    return SLASHASSIGN;
                case 336:
                    return STARASSIGN;
                case 335:
                    return MINUSASSIGN;
                case 334:
                    return PLUSASSIGN;
                case 333:
                    return LSHIFT;
                case 332:
                    return REM;
                case 331:
                    return XOR;
                case 330:
                    return BIT_OR;
                case 329:
                    return BIT_AND;
                case 328:
                    return SLASH;
                case 327:
                    return STAR;
                case 326:
                    return MINUS;
                case 325:
                    return PLUS;
                case 324:
                    return DECR;
                case 323:
                    return INCR;
                case 322:
                    return SC_OR;
                case 321:
                    return SC_AND;
                case 320:
                    return NE;
                case 319:
                    return LE;
                case 318:
                    return GE;
                case 317:
                    return EQ;
                case 316:
                    return ARROW;
                case 315:
                    return COLON;
                case 314:
                    return HOOK;
                case 313:
                    return TILDE;
                case 312:
                    return BANG;
                case 311:
                    return LT;
                case 310:
                    return ASSIGN;
                case 309:
                    return AT;
                case 308:
                    return DOT;
                case 307:
                    return COMMA;
                case 306:
                    return SEMICOLON;
                case 305:
                    return RBRACKET;
                case 304:
                    return LBRACKET;
                case 303:
                    return RBRACE;
                case 302:
                    return LBRACE;
                case 301:
                    return RPAREN;
                case 300:
                    return LPAREN;
                case 299:
                    return PART_LETTER;
                case 298:
                    return LETTER;
                case 297:
                    return IDENTIFIER;
                case 296:
                    return JML_IDENTIFIER;
                case 295:
                    return TEXT_BLOCK_CONTENT;
                case 294:
                    return TEXT_BLOCK_LITERAL;
                case 293:
                    return ENTER_TEXT_BLOCK;
                case 292:
                    return STRING_LITERAL;
                case 291:
                    return CHARACTER_LITERAL;
                case 290:
                    return UNICODE_ESCAPE;
                case 289:
                    return HEX_DIGITS;
                case 288:
                    return HEXADECIMAL_EXPONENT;
                case 287:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 286:
                    return DECIMAL_EXPONENT;
                case 285:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 284:
                    return FLOATING_POINT_LITERAL;
                case 283:
                    return BINARY_LITERAL;
                case 282:
                    return OCTAL_LITERAL;
                case 281:
                    return HEX_LITERAL;
                case 280:
                    return DECIMAL_LITERAL;
                case 279:
                    return INTEGER_LITERAL;
                case 278:
                    return LONG_LITERAL;
                case 277:
                    return TRANSITIVE;
                case 276:
                    return PROVIDES;
                case 275:
                    return EXPORTS;
                case 274:
                    return MODULE;
                case 273:
                    return USES;
                case 272:
                    return OPENS;
                case 271:
                    return OPEN;
                case 270:
                    return WITH;
                case 269:
                    return TO;
                case 268:
                    return REQUIRES;
                case 267:
                    return YIELD;
                case 266:
                    return WHILE;
                case 265:
                    return VOLATILE;
                case 264:
                    return VOID;
                case 263:
                    return TRY;
                case 262:
                    return TRUE;
                case 261:
                    return TRANSIENT;
                case 260:
                    return THROWS;
                case 259:
                    return THROW;
                case 258:
                    return THIS;
                case 257:
                    return SYNCHRONIZED;
                case 256:
                    return SWITCH;
                case 255:
                    return SUPER;
                case 254:
                    return STRICTFP;
                case 253:
                    return STATIC;
                case 252:
                    return SHORT;
                case 251:
                    return RETURN;
                case 250:
                    return PUBLIC;
                case 249:
                    return PROTECTED;
                case 248:
                    return PRIVATE;
                case 247:
                    return PACKAGE;
                case 246:
                    return NULL;
                case 245:
                    return NEW;
                case 244:
                    return NATIVE;
                case 243:
                    return LONG;
                case 242:
                    return INTERFACE;
                case 241:
                    return INT;
                case 240:
                    return INSTANCEOF;
                case 239:
                    return IMPORT;
                case 238:
                    return IMPLEMENTS;
                case 237:
                    return IF;
                case 236:
                    return GOTO;
                case 235:
                    return FOR;
                case 234:
                    return FLOAT;
                case 233:
                    return FINALLY;
                case 232:
                    return FINAL;
                case 231:
                    return FALSE;
                case 230:
                    return EXTENDS;
                case 229:
                    return ENUM;
                case 228:
                    return ELSE;
                case 227:
                    return DOUBLE;
                case 226:
                    return DO;
                case 225:
                    return _DEFAULT;
                case 224:
                    return CONTINUE;
                case 223:
                    return CONST;
                case 222:
                    return CLASS;
                case 221:
                    return CHAR;
                case 220:
                    return CATCH;
                case 219:
                    return CASE;
                case 218:
                    return BYTE;
                case 217:
                    return BREAK;
                case 216:
                    return BOOLEAN;
                case 215:
                    return ASSERT;
                case 214:
                    return ABSTRACT;
                case 213:
                    return COMMENT_CONTENT;
                case 212:
                    return MULTI_LINE_COMMENT;
                case 211:
                    return JAVADOC_COMMENT;
                case 210:
                    return ENTER_MULTILINE_COMMENT;
                case 209:
                    return ENTER_JAVADOC_COMMENT;
                case 208:
                    return INTERSECT;
                case 207:
                    return INFINITE_UNION;
                case 206:
                    return UNION;
                case 205:
                    return SUBSET;
                case 204:
                    return DISJOINT;
                case 203:
                    return NEW_OBJECTS;
                case 202:
                    return NEWELEMSFRESH;
                case 201:
                    return ALLOBJECTS;
                case 200:
                    return ALLFIELDS;
                case 199:
                    return SETMINUS;
                case 198:
                    return STATIC_INVARIANT_FOR;
                case 197:
                    return SINGLETON;
                case 196:
                    return EMPTYSET;
                case 195:
                    return LOCSET;
                case 194:
                    return WRITABLE;
                case 193:
                    return WORKING_SPACE_REDUNDANTLY;
                case 192:
                    return WORKING_SPACE;
                case 191:
                    return WORKING_SPACE_ESC;
                case 190:
                    return WHEN_REDUNDANTLY;
                case 189:
                    return WHEN;
                case 188:
                    return WARN_OP;
                case 187:
                    return WARN;
                case 186:
                    return UNREACHABLE;
                case 185:
                    return UNKNOWN_OP_EQ;
                case 184:
                    return UNKNOWN_OP;
                case 183:
                    return UNINITIALIZED;
                case 182:
                    return TYPEOF;
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
                    return SPACE_ESC;
                case 167:
                    return SIGNALS_REDUNDANTLY;
                case 166:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 165:
                    return SIGNALS_ONLY;
                case 164:
                    return SIGNALS;
                case 163:
                    return SET;
                case 162:
                    return SAME;
                case 161:
                    return SAFE_MATH;
                case 160:
                    return RETURN_BEHAVIOUR;
                case 159:
                    return RETURN_BEHAVIOR;
                case 158:
                    return RETURNS_REDUNDANTLY;
                case 157:
                    return RETURNS;
                case 156:
                    return RESULT;
                case 155:
                    return REQUIRES_REDUNDANTLY;
                case 154:
                    return REPRESENTS_REDUNDANTLY;
                case 153:
                    return REPRESENTS;
                case 152:
                    return REFINING;
                case 151:
                    return REAL;
                case 150:
                    return READABLE;
                case 149:
                    return REACH;
                case 148:
                    return PURE;
                case 147:
                    return PRODUCT;
                case 146:
                    return PRE_REDUNDANTLY;
                case 145:
                    return PRE;
                case 144:
                    return PRE_ESC;
                case 143:
                    return POST_REDUNDANTLY;
                case 142:
                    return POST;
                case 141:
                    return OR;
                case 140:
                    return ONLY_CAPTURED;
                case 139:
                    return ONLY_CALLED;
                case 138:
                    return ONLY_ASSIGNED;
                case 137:
                    return ONLY_ACCESSED;
                case 136:
                    return OLD;
                case 135:
                    return OLD_ESC;
                case 134:
                    return NUM_OF;
                case 133:
                    return NULLABLE_BY_DEFAULT;
                case 132:
                    return NULLABLE;
                case 131:
                    return NOWARN_OP;
                case 130:
                    return NOWARN;
                case 129:
                    return STRICTLY_NOTHING;
                case 128:
                    return NOT_SPECIFIED;
                case 127:
                    return NOT_MODIFIED;
                case 126:
                    return NOT_ASSIGNED;
                case 125:
                    return NOTHING;
                case 124:
                    return NORMAL_EXAMPLE;
                case 123:
                    return NORMAL_BEHAVIOUR;
                case 122:
                    return NORMAL_BEHAVIOR;
                case 121:
                    return NON_NULL;
                case 120:
                    return NONNULLELEMENTS;
                case 119:
                    return NEW_OBJECT;
                case 118:
                    return NESTED_CONTRACT_START;
                case 117:
                    return NESTED_CONTRACT_END;
                case 116:
                    return MONITORS_FOR;
                case 115:
                    return MONITORED;
                case 114:
                    return MODIFIES_redundantly;
                case 113:
                    return MODIFIES;
                case 112:
                    return MODIFIABLE_redundantly;
                case 111:
                    return MODIFIABLE;
                case 110:
                    return MODEL_PROGRAM;
                case 109:
                    return MODEL;
                case 108:
                    return MIN;
                case 107:
                    return METHOD;
                case 106:
                    return MEASURED_BY_REDUNDANTLY;
                case 105:
                    return MEASURED_BY;
                case 104:
                    return MAX;
                case 103:
                    return MAPS_REDUNDANTLY;
                case 102:
                    return MAPS;
                case 101:
                    return MAINTAINING_REDUNDANTLY;
                case 100:
                    return MAINTAINING;
                case 99:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 98:
                    return LOOP_INVARIANT;
                case 97:
                    return LOCKSET;
                case 96:
                    return LBLPOS;
                case 95:
                    return LBLNEG;
                case 94:
                    return JAVA_MATH;
                case 93:
                    return IS_INITIALIZED;
                case 92:
                    return IN_redundantly;
                case 91:
                    return INVARIANT_fOR;
                case 90:
                    return INVARIANT_REDUNDANTLY;
                case 89:
                    return INTO;
                case 88:
                    return INSTANCE;
                case 87:
                    return INITIALLY;
                case 86:
                    return INITIALIZER;
                case 85:
                    return IN;
                case 84:
                    return IMPLIES_THAT;
                case 83:
                    return HENCE_by_REDUNDANTLY;
                case 82:
                    return HENCE_by;
                case 81:
                    return HELPER;
                case 80:
                    return GHOST;
                case 79:
                    return FRESH;
                case 78:
                    return FOR_EXAMPLE;
                case 77:
                    return FORALL;
                case 76:
                    return FORALLQ;
                case 75:
                    return FIELD;
                case 74:
                    return EXTRACT;
                case 73:
                    return EXSURES_REDUNDANTLY;
                case 72:
                    return EXSURES;
                case 71:
                    return EXISTS;
                case 70:
                    return EXCEPTIONAL_EXAMPLE;
                case 69:
                    return EXCEPTIONAL_BEHAVIOUR;
                case 68:
                    return EXCEPTIONAL_BEHAVIOR;
                case 67:
                    return EXAMPLE;
                case 66:
                    return EVERYTHING;
                case 65:
                    return ERASES;
                case 64:
                    return EQUIVALENCE;
                case 63:
                    return REQUIRES_FREE;
                case 62:
                    return ENSURES_FREE;
                case 61:
                    return ENSURES_REDUNDANTLY;
                case 60:
                    return ENSURES;
                case 59:
                    return ELEMTYPE;
                case 58:
                    return DURATION_REDUNDANTLY;
                case 57:
                    return DURATION;
                case 56:
                    return DIVERGES_REDUNDANTLY;
                case 55:
                    return DIVERGES;
                case 54:
                    return DETERMINES;
                case 53:
                    return DECREASING_REDUNDANTLY;
                case 52:
                    return DECREASING;
                case 51:
                    return DECREASES_REDUNDANTLY;
                case 50:
                    return DECREASES;
                case 49:
                    return DECLASSIFIES;
                case 48:
                    return CONTINUE_BEHAVIOR;
                case 47:
                    return CONTINUES_REDUNDANTLY;
                case 46:
                    return CONTINUES;
                case 45:
                    return CONSTRUCTOR;
                case 44:
                    return CONSTRAINT_REDUNDANTLY;
                case 43:
                    return CONSTRAINT;
                case 42:
                    return CODE_SAFE_MATH;
                case 41:
                    return CODE_JAVA_MATH;
                case 40:
                    return CODE_BIGINT_MATH;
                case 39:
                    return CODE;
                case 38:
                    return CHOOSE_IF;
                case 37:
                    return CHOOSE;
                case 36:
                    return CAPTURES_REDUNDANTLY;
                case 35:
                    return CAPTURES;
                case 34:
                    return CALLABLE_REDUNDANTLY;
                case 33:
                    return CALLABLE;
                case 32:
                    return BY;
                case 31:
                    return BREAK_BEHAVIOR;
                case 30:
                    return BREAKS_REDUNDANTLY;
                case 29:
                    return BREAKS;
                case 28:
                    return BIGINT_MATH;
                case 27:
                    return BIGINT;
                case 26:
                    return BEHAVIOUR;
                case 25:
                    return BEHAVIOR;
                case 24:
                    return AXIOM;
                case 23:
                    return ASSUME_REDUNDANTLY;
                case 22:
                    return ASSUME;
                case 21:
                    return ASSIGNABLE_REDUNDANTLY;
                case 20:
                    return ASSIGNABLE;
                case 19:
                    return ASSERT_REDUNDANTLY;
                case 18:
                    return ANTIVALENCE;
                case 17:
                    return ALSO;
                case 16:
                    return ACCESSIBLE_REDUNDANTLY;
                case 15:
                    return ACCESSIBLE;
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
