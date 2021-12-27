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
        HELPER(81),
        HENCE_BY(82),
        HENCE_BY_REDUNDANTLY(83),
        IMPLIES_THAT(84),
        IN(85),
        INITIALIZER(86),
        INITIALLY(87),
        INSTANCE(88),
        TWO_STATE(89),
        NO_STATE(90),
        NON_NULL_BY_DEFAULT(91),
        INVARIANT_REDUNDANTLY(92),
        IN_REDUNDANTLY(93),
        JAVA_MATH(94),
        LBLNEG(95),
        LBLPOS(96),
        LBL(97),
        LOOP_CONTRACT(98),
        LOOP_INVARIANT(99),
        LOOP_INVARIANT_FREE(100),
        LOOP_INVARIANT_REDUNDANTLY(101),
        MAINTAINING(102),
        MAINTAINING_REDUNDANTLY(103),
        MAPS(104),
        MAPS_REDUNDANTLY(105),
        MAX(106),
        MEASURED_BY(107),
        ESC_MEASURED_BY(108),
        MEASURED_BY_REDUNDANTLY(109),
        METHOD(110),
        MIN(111),
        MODEL(112),
        MODEL_PROGRAM(113),
        MODIFIABLE(114),
        MODIFIABLE_REDUNDANTLY(115),
        LOOP_MODIFIES(116),
        MODIFIES(117),
        MODIFIES_REDUNDANTLY(118),
        MONITORED(119),
        MONITORS_FOR(120),
        NESTED_CONTRACT_END(121),
        NESTED_CONTRACT_START(122),
        NEW_OBJECT(123),
        NONNULLELEMENTS(124),
        NON_NULL(125),
        NORMAL_BEHAVIOR(126),
        NORMAL_BEHAVIOUR(127),
        FEASIBLE_BEHAVIOR(128),
        FEASIBLE_BEHAVIOUR(129),
        NORMAL_EXAMPLE(130),
        NOWARN(131),
        NOWARN_OP(132),
        NULLABLE(133),
        NULLABLE_BY_DEFAULT(134),
        NUM_OF(135),
        OLD(136),
        OR(137),
        POST(138),
        POST_REDUNDANTLY(139),
        PRE_ESC(140),
        PRE(141),
        PRE_REDUNDANTLY(142),
        PRODUCT(143),
        PURE(144),
        READABLE(145),
        REFINING(146),
        REPRESENTS(147),
        REPRESENTS_REDUNDANTLY(148),
        REQUIRES_REDUNDANTLY(149),
        RESULT(150),
        RETURNS(151),
        RETURNS_REDUNDANTLY(152),
        RETURN_BEHAVIOR(153),
        BACKARROW(154),
        RETURN_BEHAVIOUR(155),
        SAFE_MATH(156),
        SET(157),
        SIGNALS(158),
        SIGNALS_ONLY(159),
        SIGNALS_ONLY_REDUNDANTLY(160),
        SIGNALS_REDUNDANTLY(161),
        SPEC_BIGINT_MATH(162),
        SPEC_JAVA_MATH(163),
        SPEC_PACKAGE(164),
        SPEC_PRIVATE(165),
        SPEC_PROTECTED(166),
        SPEC_PUBLIC(167),
        SPEC_SAFE_MATH(168),
        STATIC_INITIALIZER(169),
        STRICTLY_PURE(170),
        SUBTYPE(171),
        SUCH_THAT(172),
        SUM(173),
        TYPE(174),
        UNINITIALIZED(175),
        UNKNOWN_OP(176),
        UNKNOWN_OP_EQ(177),
        UNREACHABLE(178),
        WARN(179),
        WARN_OP(180),
        WHEN(181),
        WHEN_REDUNDANTLY(182),
        WORKING_SPACE_ESC(183),
        WORKING_SPACE(184),
        WORKING_SPACE_REDUNDANTLY(185),
        WRITABLE(186),
        DOTDOT(187),
        JML_LINE_COMMENT(188),
        SINGLE_LINE_COMMENT(189),
        JML_ENTER_MULTILINE_COMMENT(190),
        ENTER_JAVADOC_COMMENT(191),
        ENTER_JML_BLOCK_COMMENT(192),
        ENTER_MULTILINE_COMMENT(193),
        JML_BLOCK_COMMENT(194),
        JAVADOC_COMMENT(195),
        MULTI_LINE_COMMENT(196),
        JML_MULTI_LINE_COMMENT(197),
        COMMENT_CONTENT(198),
        ABSTRACT(199),
        ASSERT(200),
        BOOLEAN(201),
        BREAK(202),
        BYTE(203),
        CASE(204),
        CATCH(205),
        CHAR(206),
        CLASS(207),
        CONST(208),
        CONTINUE(209),
        _DEFAULT(210),
        DO(211),
        DOUBLE(212),
        ELSE(213),
        ENUM(214),
        EXTENDS(215),
        FALSE(216),
        FINAL(217),
        FINALLY(218),
        FLOAT(219),
        FOR(220),
        GOTO(221),
        IF(222),
        IMPLEMENTS(223),
        IMPORT(224),
        INSTANCEOF(225),
        INT(226),
        INTERFACE(227),
        LONG(228),
        NATIVE(229),
        NEW(230),
        NULL(231),
        PACKAGE(232),
        PRIVATE(233),
        PROTECTED(234),
        PUBLIC(235),
        RECORD(236),
        RETURN(237),
        SHORT(238),
        STATIC(239),
        STRICTFP(240),
        SUPER(241),
        SWITCH(242),
        SYNCHRONIZED(243),
        THIS(244),
        THROW(245),
        THROWS(246),
        TRANSIENT(247),
        TRUE(248),
        TRY(249),
        VOID(250),
        VOLATILE(251),
        WHILE(252),
        YIELD(253),
        REQUIRES(254),
        TO(255),
        WITH(256),
        OPEN(257),
        OPENS(258),
        USES(259),
        MODULE(260),
        EXPORTS(261),
        PROVIDES(262),
        TRANSITIVE(263),
        LONG_LITERAL(264),
        INTEGER_LITERAL(265),
        DECIMAL_LITERAL(266),
        HEX_LITERAL(267),
        OCTAL_LITERAL(268),
        BINARY_LITERAL(269),
        FLOATING_POINT_LITERAL(270),
        DECIMAL_FLOATING_POINT_LITERAL(271),
        DECIMAL_EXPONENT(272),
        HEXADECIMAL_FLOATING_POINT_LITERAL(273),
        HEXADECIMAL_EXPONENT(274),
        HEX_DIGITS(275),
        UNICODE_ESCAPE(276),
        CHARACTER_LITERAL(277),
        STRING_LITERAL(278),
        ENTER_TEXT_BLOCK(279),
        TEXT_BLOCK_LITERAL(280),
        TEXT_BLOCK_CONTENT(281),
        JML_IDENTIFIER(282),
        IDENTIFIER(283),
        LETTER(284),
        PART_LETTER(285),
        LPAREN(286),
        RPAREN(287),
        LBRACE(288),
        RBRACE(289),
        LBRACKET(290),
        RBRACKET(291),
        SEMICOLON(292),
        COMMA(293),
        DOT(294),
        ELLIPSIS(295),
        AT(296),
        DOUBLECOLON(297),
        ASSIGN(298),
        LT(299),
        BANG(300),
        TILDE(301),
        HOOK(302),
        COLON(303),
        ARROW(304),
        EQ(305),
        GE(306),
        LE(307),
        NE(308),
        SC_AND(309),
        SC_OR(310),
        INCR(311),
        DECR(312),
        PLUS(313),
        MINUS(314),
        STAR(315),
        SLASH(316),
        BIT_AND(317),
        BIT_OR(318),
        XOR(319),
        REM(320),
        LSHIFT(321),
        PLUSASSIGN(322),
        MINUSASSIGN(323),
        STARASSIGN(324),
        SLASHASSIGN(325),
        ANDASSIGN(326),
        ORASSIGN(327),
        XORASSIGN(328),
        REMASSIGN(329),
        LSHIFTASSIGN(330),
        RSIGNEDSHIFTASSIGN(331),
        RUNSIGNEDSHIFTASSIGN(332),
        RUNSIGNEDSHIFT(333),
        RSIGNEDSHIFT(334),
        GT(335),
        CTRL_Z(336);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 336:
                    return CTRL_Z;
                case 335:
                    return GT;
                case 334:
                    return RSIGNEDSHIFT;
                case 333:
                    return RUNSIGNEDSHIFT;
                case 332:
                    return RUNSIGNEDSHIFTASSIGN;
                case 331:
                    return RSIGNEDSHIFTASSIGN;
                case 330:
                    return LSHIFTASSIGN;
                case 329:
                    return REMASSIGN;
                case 328:
                    return XORASSIGN;
                case 327:
                    return ORASSIGN;
                case 326:
                    return ANDASSIGN;
                case 325:
                    return SLASHASSIGN;
                case 324:
                    return STARASSIGN;
                case 323:
                    return MINUSASSIGN;
                case 322:
                    return PLUSASSIGN;
                case 321:
                    return LSHIFT;
                case 320:
                    return REM;
                case 319:
                    return XOR;
                case 318:
                    return BIT_OR;
                case 317:
                    return BIT_AND;
                case 316:
                    return SLASH;
                case 315:
                    return STAR;
                case 314:
                    return MINUS;
                case 313:
                    return PLUS;
                case 312:
                    return DECR;
                case 311:
                    return INCR;
                case 310:
                    return SC_OR;
                case 309:
                    return SC_AND;
                case 308:
                    return NE;
                case 307:
                    return LE;
                case 306:
                    return GE;
                case 305:
                    return EQ;
                case 304:
                    return ARROW;
                case 303:
                    return COLON;
                case 302:
                    return HOOK;
                case 301:
                    return TILDE;
                case 300:
                    return BANG;
                case 299:
                    return LT;
                case 298:
                    return ASSIGN;
                case 297:
                    return DOUBLECOLON;
                case 296:
                    return AT;
                case 295:
                    return ELLIPSIS;
                case 294:
                    return DOT;
                case 293:
                    return COMMA;
                case 292:
                    return SEMICOLON;
                case 291:
                    return RBRACKET;
                case 290:
                    return LBRACKET;
                case 289:
                    return RBRACE;
                case 288:
                    return LBRACE;
                case 287:
                    return RPAREN;
                case 286:
                    return LPAREN;
                case 285:
                    return PART_LETTER;
                case 284:
                    return LETTER;
                case 283:
                    return IDENTIFIER;
                case 282:
                    return JML_IDENTIFIER;
                case 281:
                    return TEXT_BLOCK_CONTENT;
                case 280:
                    return TEXT_BLOCK_LITERAL;
                case 279:
                    return ENTER_TEXT_BLOCK;
                case 278:
                    return STRING_LITERAL;
                case 277:
                    return CHARACTER_LITERAL;
                case 276:
                    return UNICODE_ESCAPE;
                case 275:
                    return HEX_DIGITS;
                case 274:
                    return HEXADECIMAL_EXPONENT;
                case 273:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 272:
                    return DECIMAL_EXPONENT;
                case 271:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 270:
                    return FLOATING_POINT_LITERAL;
                case 269:
                    return BINARY_LITERAL;
                case 268:
                    return OCTAL_LITERAL;
                case 267:
                    return HEX_LITERAL;
                case 266:
                    return DECIMAL_LITERAL;
                case 265:
                    return INTEGER_LITERAL;
                case 264:
                    return LONG_LITERAL;
                case 263:
                    return TRANSITIVE;
                case 262:
                    return PROVIDES;
                case 261:
                    return EXPORTS;
                case 260:
                    return MODULE;
                case 259:
                    return USES;
                case 258:
                    return OPENS;
                case 257:
                    return OPEN;
                case 256:
                    return WITH;
                case 255:
                    return TO;
                case 254:
                    return REQUIRES;
                case 253:
                    return YIELD;
                case 252:
                    return WHILE;
                case 251:
                    return VOLATILE;
                case 250:
                    return VOID;
                case 249:
                    return TRY;
                case 248:
                    return TRUE;
                case 247:
                    return TRANSIENT;
                case 246:
                    return THROWS;
                case 245:
                    return THROW;
                case 244:
                    return THIS;
                case 243:
                    return SYNCHRONIZED;
                case 242:
                    return SWITCH;
                case 241:
                    return SUPER;
                case 240:
                    return STRICTFP;
                case 239:
                    return STATIC;
                case 238:
                    return SHORT;
                case 237:
                    return RETURN;
                case 236:
                    return RECORD;
                case 235:
                    return PUBLIC;
                case 234:
                    return PROTECTED;
                case 233:
                    return PRIVATE;
                case 232:
                    return PACKAGE;
                case 231:
                    return NULL;
                case 230:
                    return NEW;
                case 229:
                    return NATIVE;
                case 228:
                    return LONG;
                case 227:
                    return INTERFACE;
                case 226:
                    return INT;
                case 225:
                    return INSTANCEOF;
                case 224:
                    return IMPORT;
                case 223:
                    return IMPLEMENTS;
                case 222:
                    return IF;
                case 221:
                    return GOTO;
                case 220:
                    return FOR;
                case 219:
                    return FLOAT;
                case 218:
                    return FINALLY;
                case 217:
                    return FINAL;
                case 216:
                    return FALSE;
                case 215:
                    return EXTENDS;
                case 214:
                    return ENUM;
                case 213:
                    return ELSE;
                case 212:
                    return DOUBLE;
                case 211:
                    return DO;
                case 210:
                    return _DEFAULT;
                case 209:
                    return CONTINUE;
                case 208:
                    return CONST;
                case 207:
                    return CLASS;
                case 206:
                    return CHAR;
                case 205:
                    return CATCH;
                case 204:
                    return CASE;
                case 203:
                    return BYTE;
                case 202:
                    return BREAK;
                case 201:
                    return BOOLEAN;
                case 200:
                    return ASSERT;
                case 199:
                    return ABSTRACT;
                case 198:
                    return COMMENT_CONTENT;
                case 197:
                    return JML_MULTI_LINE_COMMENT;
                case 196:
                    return MULTI_LINE_COMMENT;
                case 195:
                    return JAVADOC_COMMENT;
                case 194:
                    return JML_BLOCK_COMMENT;
                case 193:
                    return ENTER_MULTILINE_COMMENT;
                case 192:
                    return ENTER_JML_BLOCK_COMMENT;
                case 191:
                    return ENTER_JAVADOC_COMMENT;
                case 190:
                    return JML_ENTER_MULTILINE_COMMENT;
                case 189:
                    return SINGLE_LINE_COMMENT;
                case 188:
                    return JML_LINE_COMMENT;
                case 187:
                    return DOTDOT;
                case 186:
                    return WRITABLE;
                case 185:
                    return WORKING_SPACE_REDUNDANTLY;
                case 184:
                    return WORKING_SPACE;
                case 183:
                    return WORKING_SPACE_ESC;
                case 182:
                    return WHEN_REDUNDANTLY;
                case 181:
                    return WHEN;
                case 180:
                    return WARN_OP;
                case 179:
                    return WARN;
                case 178:
                    return UNREACHABLE;
                case 177:
                    return UNKNOWN_OP_EQ;
                case 176:
                    return UNKNOWN_OP;
                case 175:
                    return UNINITIALIZED;
                case 174:
                    return TYPE;
                case 173:
                    return SUM;
                case 172:
                    return SUCH_THAT;
                case 171:
                    return SUBTYPE;
                case 170:
                    return STRICTLY_PURE;
                case 169:
                    return STATIC_INITIALIZER;
                case 168:
                    return SPEC_SAFE_MATH;
                case 167:
                    return SPEC_PUBLIC;
                case 166:
                    return SPEC_PROTECTED;
                case 165:
                    return SPEC_PRIVATE;
                case 164:
                    return SPEC_PACKAGE;
                case 163:
                    return SPEC_JAVA_MATH;
                case 162:
                    return SPEC_BIGINT_MATH;
                case 161:
                    return SIGNALS_REDUNDANTLY;
                case 160:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 159:
                    return SIGNALS_ONLY;
                case 158:
                    return SIGNALS;
                case 157:
                    return SET;
                case 156:
                    return SAFE_MATH;
                case 155:
                    return RETURN_BEHAVIOUR;
                case 154:
                    return BACKARROW;
                case 153:
                    return RETURN_BEHAVIOR;
                case 152:
                    return RETURNS_REDUNDANTLY;
                case 151:
                    return RETURNS;
                case 150:
                    return RESULT;
                case 149:
                    return REQUIRES_REDUNDANTLY;
                case 148:
                    return REPRESENTS_REDUNDANTLY;
                case 147:
                    return REPRESENTS;
                case 146:
                    return REFINING;
                case 145:
                    return READABLE;
                case 144:
                    return PURE;
                case 143:
                    return PRODUCT;
                case 142:
                    return PRE_REDUNDANTLY;
                case 141:
                    return PRE;
                case 140:
                    return PRE_ESC;
                case 139:
                    return POST_REDUNDANTLY;
                case 138:
                    return POST;
                case 137:
                    return OR;
                case 136:
                    return OLD;
                case 135:
                    return NUM_OF;
                case 134:
                    return NULLABLE_BY_DEFAULT;
                case 133:
                    return NULLABLE;
                case 132:
                    return NOWARN_OP;
                case 131:
                    return NOWARN;
                case 130:
                    return NORMAL_EXAMPLE;
                case 129:
                    return FEASIBLE_BEHAVIOUR;
                case 128:
                    return FEASIBLE_BEHAVIOR;
                case 127:
                    return NORMAL_BEHAVIOUR;
                case 126:
                    return NORMAL_BEHAVIOR;
                case 125:
                    return NON_NULL;
                case 124:
                    return NONNULLELEMENTS;
                case 123:
                    return NEW_OBJECT;
                case 122:
                    return NESTED_CONTRACT_START;
                case 121:
                    return NESTED_CONTRACT_END;
                case 120:
                    return MONITORS_FOR;
                case 119:
                    return MONITORED;
                case 118:
                    return MODIFIES_REDUNDANTLY;
                case 117:
                    return MODIFIES;
                case 116:
                    return LOOP_MODIFIES;
                case 115:
                    return MODIFIABLE_REDUNDANTLY;
                case 114:
                    return MODIFIABLE;
                case 113:
                    return MODEL_PROGRAM;
                case 112:
                    return MODEL;
                case 111:
                    return MIN;
                case 110:
                    return METHOD;
                case 109:
                    return MEASURED_BY_REDUNDANTLY;
                case 108:
                    return ESC_MEASURED_BY;
                case 107:
                    return MEASURED_BY;
                case 106:
                    return MAX;
                case 105:
                    return MAPS_REDUNDANTLY;
                case 104:
                    return MAPS;
                case 103:
                    return MAINTAINING_REDUNDANTLY;
                case 102:
                    return MAINTAINING;
                case 101:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 100:
                    return LOOP_INVARIANT_FREE;
                case 99:
                    return LOOP_INVARIANT;
                case 98:
                    return LOOP_CONTRACT;
                case 97:
                    return LBL;
                case 96:
                    return LBLPOS;
                case 95:
                    return LBLNEG;
                case 94:
                    return JAVA_MATH;
                case 93:
                    return IN_REDUNDANTLY;
                case 92:
                    return INVARIANT_REDUNDANTLY;
                case 91:
                    return NON_NULL_BY_DEFAULT;
                case 90:
                    return NO_STATE;
                case 89:
                    return TWO_STATE;
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
                    return HENCE_BY_REDUNDANTLY;
                case 82:
                    return HENCE_BY;
                case 81:
                    return HELPER;
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
