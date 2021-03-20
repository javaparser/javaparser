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
        EQUIVALENCE(62),
        ERASES(63),
        EVERYTHING(64),
        EXAMPLE(65),
        EXCEPTIONAL_BEHAVIOR(66),
        EXCEPTIONAL_BEHAVIOUR(67),
        EXCEPTIONAL_EXAMPLE(68),
        EXISTS(69),
        EXSURES(70),
        EXSURES_REDUNDANTLY(71),
        EXTRACT(72),
        FIELD(73),
        FORALLQ(74),
        FORALL(75),
        FOR_EXAMPLE(76),
        FRESH(77),
        GHOST(78),
        HELPER(79),
        HENCE_by(80),
        HENCE_by_REDUNDANTLY(81),
        IMPLIES_THAT(82),
        IN(83),
        INITIALIZER(84),
        INITIALLY(85),
        INSTANCE(86),
        INTO(87),
        INVARIANT_REDUNDANTLY(88),
        INVARIANT_fOR(89),
        IN_redundantly(90),
        IS_INITIALIZED(91),
        JAVA_MATH(92),
        LBLNEG(93),
        LBLPOS(94),
        LOCKSET(95),
        LOOP_INVARIANT(96),
        LOOP_INVARIANT_REDUNDANTLY(97),
        MAINTAINING(98),
        MAINTAINING_REDUNDANTLY(99),
        MAPS(100),
        MAPS_REDUNDANTLY(101),
        MAX(102),
        MEASURED_BY(103),
        MEASURED_BY_REDUNDANTLY(104),
        METHOD(105),
        MIN(106),
        MODEL(107),
        MODEL_PROGRAM(108),
        MODIFIABLE(109),
        MODIFIABLE_redundantly(110),
        MODIFIES(111),
        MODIFIES_redundantly(112),
        MONITORED(113),
        MONITORS_FOR(114),
        NESTED_CONTRACT_END(115),
        NESTED_CONTRACT_START(116),
        NEW_OBJECT(117),
        NONNULLELEMENTS(118),
        NON_NULL(119),
        NORMAL_BEHAVIOR(120),
        NORMAL_BEHAVIOUR(121),
        NORMAL_EXAMPLE(122),
        NOTHING(123),
        NOT_ASSIGNED(124),
        NOT_MODIFIED(125),
        NOT_SPECIFIED(126),
        STRICTLY_NOTHING(127),
        NOWARN(128),
        NOWARN_OP(129),
        NULLABLE(130),
        NULLABLE_BY_DEFAULT(131),
        NUM_OF(132),
        OLD_ESC(133),
        OLD(134),
        ONLY_ACCESSED(135),
        ONLY_ASSIGNED(136),
        ONLY_CALLED(137),
        ONLY_CAPTURED(138),
        OR(139),
        POST(140),
        POST_REDUNDANTLY(141),
        PRE_ESC(142),
        PRE(143),
        PRE_REDUNDANTLY(144),
        PRODUCT(145),
        PURE(146),
        REACH(147),
        READABLE(148),
        REAL(149),
        REFINING(150),
        REPRESENTS(151),
        REPRESENTS_REDUNDANTLY(152),
        REQUIRES_REDUNDANTLY(153),
        RESULT(154),
        RETURNS(155),
        RETURNS_REDUNDANTLY(156),
        RETURN_BEHAVIOR(157),
        SAFE_MATH(158),
        SAME(159),
        SET(160),
        SIGNALS(161),
        SIGNALS_ONLY(162),
        SIGNALS_ONLY_REDUNDANTLY(163),
        SIGNALS_REDUNDANTLY(164),
        SPACE_ESC(165),
        SPEC_BIGINT_MATH(166),
        SPEC_JAVA_MATH(167),
        SPEC_PACKAGE(168),
        SPEC_PRIVATE(169),
        SPEC_PROTECTED(170),
        SPEC_PUBLIC(171),
        SPEC_SAFE_MATH(172),
        STATIC_INITIALIZER(173),
        STRICTLY_PURE(174),
        SUBTYPE(175),
        SUCH_THAT(176),
        SUM(177),
        TYPE(178),
        TYPEOF(179),
        UNINITIALIZED(180),
        UNKNOWN_OP(181),
        UNKNOWN_OP_EQ(182),
        UNREACHABLE(183),
        WARN(184),
        WARN_OP(185),
        WHEN(186),
        WHEN_REDUNDANTLY(187),
        WORKING_SPACE_ESC(188),
        WORKING_SPACE(189),
        WORKING_SPACE_REDUNDANTLY(190),
        WRITABLE(191),
        LOCSET(192),
        EMPTYSET(193),
        SINGLETON(194),
        STATIC_INVARIANT_FOR(195),
        SETMINUS(196),
        ALLFIELDS(197),
        ALLOBJECTS(198),
        NEWELEMSFRESH(199),
        NEW_OBJECTS(200),
        DISJOINT(201),
        SUBSET(202),
        UNION(203),
        INFINITE_UNION(204),
        INTERSECT(205),
        ENTER_JAVADOC_COMMENT(206),
        ENTER_MULTILINE_COMMENT(207),
        JAVADOC_COMMENT(208),
        MULTI_LINE_COMMENT(209),
        COMMENT_CONTENT(210),
        ABSTRACT(211),
        ASSERT(212),
        BOOLEAN(213),
        BREAK(214),
        BYTE(215),
        CASE(216),
        CATCH(217),
        CHAR(218),
        CLASS(219),
        CONST(220),
        CONTINUE(221),
        _DEFAULT(222),
        DO(223),
        DOUBLE(224),
        ELSE(225),
        ENUM(226),
        EXTENDS(227),
        FALSE(228),
        FINAL(229),
        FINALLY(230),
        FLOAT(231),
        FOR(232),
        GOTO(233),
        IF(234),
        IMPLEMENTS(235),
        IMPORT(236),
        INSTANCEOF(237),
        INT(238),
        INTERFACE(239),
        LONG(240),
        NATIVE(241),
        NEW(242),
        NULL(243),
        PACKAGE(244),
        PRIVATE(245),
        PROTECTED(246),
        PUBLIC(247),
        RETURN(248),
        SHORT(249),
        STATIC(250),
        STRICTFP(251),
        SUPER(252),
        SWITCH(253),
        SYNCHRONIZED(254),
        THIS(255),
        THROW(256),
        THROWS(257),
        TRANSIENT(258),
        TRUE(259),
        TRY(260),
        VOID(261),
        VOLATILE(262),
        WHILE(263),
        YIELD(264),
        REQUIRES(265),
        TO(266),
        WITH(267),
        OPEN(268),
        OPENS(269),
        USES(270),
        MODULE(271),
        EXPORTS(272),
        PROVIDES(273),
        TRANSITIVE(274),
        LONG_LITERAL(275),
        INTEGER_LITERAL(276),
        DECIMAL_LITERAL(277),
        HEX_LITERAL(278),
        OCTAL_LITERAL(279),
        BINARY_LITERAL(280),
        FLOATING_POINT_LITERAL(281),
        DECIMAL_FLOATING_POINT_LITERAL(282),
        DECIMAL_EXPONENT(283),
        HEXADECIMAL_FLOATING_POINT_LITERAL(284),
        HEXADECIMAL_EXPONENT(285),
        HEX_DIGITS(286),
        UNICODE_ESCAPE(287),
        CHARACTER_LITERAL(288),
        STRING_LITERAL(289),
        ENTER_TEXT_BLOCK(290),
        TEXT_BLOCK_LITERAL(291),
        TEXT_BLOCK_CONTENT(292),
        IDENTIFIER(293),
        LETTER(294),
        PART_LETTER(295),
        LPAREN(296),
        RPAREN(297),
        LBRACE(298),
        RBRACE(299),
        LBRACKET(300),
        RBRACKET(301),
        SEMICOLON(302),
        COMMA(303),
        DOT(304),
        AT(305),
        ASSIGN(306),
        LT(307),
        BANG(308),
        TILDE(309),
        HOOK(310),
        COLON(311),
        ARROW(312),
        EQ(313),
        GE(314),
        LE(315),
        NE(316),
        SC_AND(317),
        SC_OR(318),
        INCR(319),
        DECR(320),
        PLUS(321),
        MINUS(322),
        STAR(323),
        SLASH(324),
        BIT_AND(325),
        BIT_OR(326),
        XOR(327),
        REM(328),
        LSHIFT(329),
        PLUSASSIGN(330),
        MINUSASSIGN(331),
        STARASSIGN(332),
        SLASHASSIGN(333),
        ANDASSIGN(334),
        ORASSIGN(335),
        XORASSIGN(336),
        REMASSIGN(337),
        LSHIFTASSIGN(338),
        RSIGNEDSHIFTASSIGN(339),
        RUNSIGNEDSHIFTASSIGN(340),
        ELLIPSIS(341),
        DOUBLECOLON(342),
        RUNSIGNEDSHIFT(343),
        RSIGNEDSHIFT(344),
        GT(345),
        CTRL_Z(346);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 346:
                    return CTRL_Z;
                case 345:
                    return GT;
                case 344:
                    return RSIGNEDSHIFT;
                case 343:
                    return RUNSIGNEDSHIFT;
                case 342:
                    return DOUBLECOLON;
                case 341:
                    return ELLIPSIS;
                case 340:
                    return RUNSIGNEDSHIFTASSIGN;
                case 339:
                    return RSIGNEDSHIFTASSIGN;
                case 338:
                    return LSHIFTASSIGN;
                case 337:
                    return REMASSIGN;
                case 336:
                    return XORASSIGN;
                case 335:
                    return ORASSIGN;
                case 334:
                    return ANDASSIGN;
                case 333:
                    return SLASHASSIGN;
                case 332:
                    return STARASSIGN;
                case 331:
                    return MINUSASSIGN;
                case 330:
                    return PLUSASSIGN;
                case 329:
                    return LSHIFT;
                case 328:
                    return REM;
                case 327:
                    return XOR;
                case 326:
                    return BIT_OR;
                case 325:
                    return BIT_AND;
                case 324:
                    return SLASH;
                case 323:
                    return STAR;
                case 322:
                    return MINUS;
                case 321:
                    return PLUS;
                case 320:
                    return DECR;
                case 319:
                    return INCR;
                case 318:
                    return SC_OR;
                case 317:
                    return SC_AND;
                case 316:
                    return NE;
                case 315:
                    return LE;
                case 314:
                    return GE;
                case 313:
                    return EQ;
                case 312:
                    return ARROW;
                case 311:
                    return COLON;
                case 310:
                    return HOOK;
                case 309:
                    return TILDE;
                case 308:
                    return BANG;
                case 307:
                    return LT;
                case 306:
                    return ASSIGN;
                case 305:
                    return AT;
                case 304:
                    return DOT;
                case 303:
                    return COMMA;
                case 302:
                    return SEMICOLON;
                case 301:
                    return RBRACKET;
                case 300:
                    return LBRACKET;
                case 299:
                    return RBRACE;
                case 298:
                    return LBRACE;
                case 297:
                    return RPAREN;
                case 296:
                    return LPAREN;
                case 295:
                    return PART_LETTER;
                case 294:
                    return LETTER;
                case 293:
                    return IDENTIFIER;
                case 292:
                    return TEXT_BLOCK_CONTENT;
                case 291:
                    return TEXT_BLOCK_LITERAL;
                case 290:
                    return ENTER_TEXT_BLOCK;
                case 289:
                    return STRING_LITERAL;
                case 288:
                    return CHARACTER_LITERAL;
                case 287:
                    return UNICODE_ESCAPE;
                case 286:
                    return HEX_DIGITS;
                case 285:
                    return HEXADECIMAL_EXPONENT;
                case 284:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 283:
                    return DECIMAL_EXPONENT;
                case 282:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 281:
                    return FLOATING_POINT_LITERAL;
                case 280:
                    return BINARY_LITERAL;
                case 279:
                    return OCTAL_LITERAL;
                case 278:
                    return HEX_LITERAL;
                case 277:
                    return DECIMAL_LITERAL;
                case 276:
                    return INTEGER_LITERAL;
                case 275:
                    return LONG_LITERAL;
                case 274:
                    return TRANSITIVE;
                case 273:
                    return PROVIDES;
                case 272:
                    return EXPORTS;
                case 271:
                    return MODULE;
                case 270:
                    return USES;
                case 269:
                    return OPENS;
                case 268:
                    return OPEN;
                case 267:
                    return WITH;
                case 266:
                    return TO;
                case 265:
                    return REQUIRES;
                case 264:
                    return YIELD;
                case 263:
                    return WHILE;
                case 262:
                    return VOLATILE;
                case 261:
                    return VOID;
                case 260:
                    return TRY;
                case 259:
                    return TRUE;
                case 258:
                    return TRANSIENT;
                case 257:
                    return THROWS;
                case 256:
                    return THROW;
                case 255:
                    return THIS;
                case 254:
                    return SYNCHRONIZED;
                case 253:
                    return SWITCH;
                case 252:
                    return SUPER;
                case 251:
                    return STRICTFP;
                case 250:
                    return STATIC;
                case 249:
                    return SHORT;
                case 248:
                    return RETURN;
                case 247:
                    return PUBLIC;
                case 246:
                    return PROTECTED;
                case 245:
                    return PRIVATE;
                case 244:
                    return PACKAGE;
                case 243:
                    return NULL;
                case 242:
                    return NEW;
                case 241:
                    return NATIVE;
                case 240:
                    return LONG;
                case 239:
                    return INTERFACE;
                case 238:
                    return INT;
                case 237:
                    return INSTANCEOF;
                case 236:
                    return IMPORT;
                case 235:
                    return IMPLEMENTS;
                case 234:
                    return IF;
                case 233:
                    return GOTO;
                case 232:
                    return FOR;
                case 231:
                    return FLOAT;
                case 230:
                    return FINALLY;
                case 229:
                    return FINAL;
                case 228:
                    return FALSE;
                case 227:
                    return EXTENDS;
                case 226:
                    return ENUM;
                case 225:
                    return ELSE;
                case 224:
                    return DOUBLE;
                case 223:
                    return DO;
                case 222:
                    return _DEFAULT;
                case 221:
                    return CONTINUE;
                case 220:
                    return CONST;
                case 219:
                    return CLASS;
                case 218:
                    return CHAR;
                case 217:
                    return CATCH;
                case 216:
                    return CASE;
                case 215:
                    return BYTE;
                case 214:
                    return BREAK;
                case 213:
                    return BOOLEAN;
                case 212:
                    return ASSERT;
                case 211:
                    return ABSTRACT;
                case 210:
                    return COMMENT_CONTENT;
                case 209:
                    return MULTI_LINE_COMMENT;
                case 208:
                    return JAVADOC_COMMENT;
                case 207:
                    return ENTER_MULTILINE_COMMENT;
                case 206:
                    return ENTER_JAVADOC_COMMENT;
                case 205:
                    return INTERSECT;
                case 204:
                    return INFINITE_UNION;
                case 203:
                    return UNION;
                case 202:
                    return SUBSET;
                case 201:
                    return DISJOINT;
                case 200:
                    return NEW_OBJECTS;
                case 199:
                    return NEWELEMSFRESH;
                case 198:
                    return ALLOBJECTS;
                case 197:
                    return ALLFIELDS;
                case 196:
                    return SETMINUS;
                case 195:
                    return STATIC_INVARIANT_FOR;
                case 194:
                    return SINGLETON;
                case 193:
                    return EMPTYSET;
                case 192:
                    return LOCSET;
                case 191:
                    return WRITABLE;
                case 190:
                    return WORKING_SPACE_REDUNDANTLY;
                case 189:
                    return WORKING_SPACE;
                case 188:
                    return WORKING_SPACE_ESC;
                case 187:
                    return WHEN_REDUNDANTLY;
                case 186:
                    return WHEN;
                case 185:
                    return WARN_OP;
                case 184:
                    return WARN;
                case 183:
                    return UNREACHABLE;
                case 182:
                    return UNKNOWN_OP_EQ;
                case 181:
                    return UNKNOWN_OP;
                case 180:
                    return UNINITIALIZED;
                case 179:
                    return TYPEOF;
                case 178:
                    return TYPE;
                case 177:
                    return SUM;
                case 176:
                    return SUCH_THAT;
                case 175:
                    return SUBTYPE;
                case 174:
                    return STRICTLY_PURE;
                case 173:
                    return STATIC_INITIALIZER;
                case 172:
                    return SPEC_SAFE_MATH;
                case 171:
                    return SPEC_PUBLIC;
                case 170:
                    return SPEC_PROTECTED;
                case 169:
                    return SPEC_PRIVATE;
                case 168:
                    return SPEC_PACKAGE;
                case 167:
                    return SPEC_JAVA_MATH;
                case 166:
                    return SPEC_BIGINT_MATH;
                case 165:
                    return SPACE_ESC;
                case 164:
                    return SIGNALS_REDUNDANTLY;
                case 163:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 162:
                    return SIGNALS_ONLY;
                case 161:
                    return SIGNALS;
                case 160:
                    return SET;
                case 159:
                    return SAME;
                case 158:
                    return SAFE_MATH;
                case 157:
                    return RETURN_BEHAVIOR;
                case 156:
                    return RETURNS_REDUNDANTLY;
                case 155:
                    return RETURNS;
                case 154:
                    return RESULT;
                case 153:
                    return REQUIRES_REDUNDANTLY;
                case 152:
                    return REPRESENTS_REDUNDANTLY;
                case 151:
                    return REPRESENTS;
                case 150:
                    return REFINING;
                case 149:
                    return REAL;
                case 148:
                    return READABLE;
                case 147:
                    return REACH;
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
                    return ONLY_CAPTURED;
                case 137:
                    return ONLY_CALLED;
                case 136:
                    return ONLY_ASSIGNED;
                case 135:
                    return ONLY_ACCESSED;
                case 134:
                    return OLD;
                case 133:
                    return OLD_ESC;
                case 132:
                    return NUM_OF;
                case 131:
                    return NULLABLE_BY_DEFAULT;
                case 130:
                    return NULLABLE;
                case 129:
                    return NOWARN_OP;
                case 128:
                    return NOWARN;
                case 127:
                    return STRICTLY_NOTHING;
                case 126:
                    return NOT_SPECIFIED;
                case 125:
                    return NOT_MODIFIED;
                case 124:
                    return NOT_ASSIGNED;
                case 123:
                    return NOTHING;
                case 122:
                    return NORMAL_EXAMPLE;
                case 121:
                    return NORMAL_BEHAVIOUR;
                case 120:
                    return NORMAL_BEHAVIOR;
                case 119:
                    return NON_NULL;
                case 118:
                    return NONNULLELEMENTS;
                case 117:
                    return NEW_OBJECT;
                case 116:
                    return NESTED_CONTRACT_START;
                case 115:
                    return NESTED_CONTRACT_END;
                case 114:
                    return MONITORS_FOR;
                case 113:
                    return MONITORED;
                case 112:
                    return MODIFIES_redundantly;
                case 111:
                    return MODIFIES;
                case 110:
                    return MODIFIABLE_redundantly;
                case 109:
                    return MODIFIABLE;
                case 108:
                    return MODEL_PROGRAM;
                case 107:
                    return MODEL;
                case 106:
                    return MIN;
                case 105:
                    return METHOD;
                case 104:
                    return MEASURED_BY_REDUNDANTLY;
                case 103:
                    return MEASURED_BY;
                case 102:
                    return MAX;
                case 101:
                    return MAPS_REDUNDANTLY;
                case 100:
                    return MAPS;
                case 99:
                    return MAINTAINING_REDUNDANTLY;
                case 98:
                    return MAINTAINING;
                case 97:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 96:
                    return LOOP_INVARIANT;
                case 95:
                    return LOCKSET;
                case 94:
                    return LBLPOS;
                case 93:
                    return LBLNEG;
                case 92:
                    return JAVA_MATH;
                case 91:
                    return IS_INITIALIZED;
                case 90:
                    return IN_redundantly;
                case 89:
                    return INVARIANT_fOR;
                case 88:
                    return INVARIANT_REDUNDANTLY;
                case 87:
                    return INTO;
                case 86:
                    return INSTANCE;
                case 85:
                    return INITIALLY;
                case 84:
                    return INITIALIZER;
                case 83:
                    return IN;
                case 82:
                    return IMPLIES_THAT;
                case 81:
                    return HENCE_by_REDUNDANTLY;
                case 80:
                    return HENCE_by;
                case 79:
                    return HELPER;
                case 78:
                    return GHOST;
                case 77:
                    return FRESH;
                case 76:
                    return FOR_EXAMPLE;
                case 75:
                    return FORALL;
                case 74:
                    return FORALLQ;
                case 73:
                    return FIELD;
                case 72:
                    return EXTRACT;
                case 71:
                    return EXSURES_REDUNDANTLY;
                case 70:
                    return EXSURES;
                case 69:
                    return EXISTS;
                case 68:
                    return EXCEPTIONAL_EXAMPLE;
                case 67:
                    return EXCEPTIONAL_BEHAVIOUR;
                case 66:
                    return EXCEPTIONAL_BEHAVIOR;
                case 65:
                    return EXAMPLE;
                case 64:
                    return EVERYTHING;
                case 63:
                    return ERASES;
                case 62:
                    return EQUIVALENCE;
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
