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
        CONSTRAINT(38),
        CONSTRAINT_REDUNDANTLY(39),
        CONSTRUCTOR(40),
        CONTINUES(41),
        CONTINUES_REDUNDANTLY(42),
        CONTINUE_BEHAVIOR(43),
        CONTINUE_BEHAVIOUR(44),
        DECLASSIFIES(45),
        DECREASES(46),
        DECREASES_REDUNDANTLY(47),
        DECREASING(48),
        DECREASING_REDUNDANTLY(49),
        DETERMINES(50),
        DIVERGES(51),
        DIVERGES_REDUNDANTLY(52),
        DURATION(53),
        DURATION_REDUNDANTLY(54),
        ENSURES(55),
        ENSURES_REDUNDANTLY(56),
        ENSURES_FREE(57),
        REQUIRES_FREE(58),
        EQUIVALENCE(59),
        IMPLICATION(60),
        IMPLICATION_BACKWARD(61),
        ERASES(62),
        EXAMPLE(63),
        EXCEPTIONAL_BEHAVIOR(64),
        EXCEPTIONAL_BEHAVIOUR(65),
        EXCEPTIONAL_EXAMPLE(66),
        EXISTS(67),
        EXSURES(68),
        EXSURES_REDUNDANTLY(69),
        EXTRACT(70),
        FIELD(71),
        FORALLQ(72),
        LET(73),
        FORALL(74),
        FOR_EXAMPLE(75),
        GHOST(76),
        HELPER(77),
        HENCE_BY(78),
        HENCE_BY_REDUNDANTLY(79),
        IMPLIES_THAT(80),
        IN(81),
        INITIALIZER(82),
        INITIALLY(83),
        INSTANCE(84),
        TWO_STATE(85),
        NO_STATE(86),
        NON_NULL_BY_DEFAULT(87),
        INVARIANT_REDUNDANTLY(88),
        IN_REDUNDANTLY(89),
        JAVA_MATH(90),
        LBLNEG(91),
        LBLPOS(92),
        LBL(93),
        LOOP_CONTRACT(94),
        LOOP_INVARIANT(95),
        LOOP_INVARIANT_FREE(96),
        LOOP_INVARIANT_REDUNDANTLY(97),
        MAINTAINING(98),
        MAINTAINING_REDUNDANTLY(99),
        MAPS(100),
        MAPS_REDUNDANTLY(101),
        MAX(102),
        MEASURED_BY(103),
        ESC_MEASURED_BY(104),
        MEASURED_BY_REDUNDANTLY(105),
        METHOD(106),
        MIN(107),
        MODEL(108),
        MODEL_PROGRAM(109),
        MODIFIABLE(110),
        MODIFIABLE_REDUNDANTLY(111),
        LOOP_MODIFIES(112),
        MODIFIES(113),
        MODIFIES_REDUNDANTLY(114),
        MONITORED(115),
        MONITORS_FOR(116),
        NESTED_CONTRACT_END(117),
        NESTED_CONTRACT_START(118),
        NEW_OBJECT(119),
        NONNULLELEMENTS(120),
        NON_NULL(121),
        NORMAL_BEHAVIOR(122),
        NORMAL_BEHAVIOUR(123),
        FEASIBLE_BEHAVIOR(124),
        FEASIBLE_BEHAVIOUR(125),
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
        READABLE(141),
        REFINING(142),
        REPRESENTS(143),
        REPRESENTS_REDUNDANTLY(144),
        REQUIRES_REDUNDANTLY(145),
        RESULT(146),
        RETURNS(147),
        RETURNS_REDUNDANTLY(148),
        RETURN_BEHAVIOR(149),
        BACKARROW(150),
        RETURN_BEHAVIOUR(151),
        SAFE_MATH(152),
        SET(153),
        SIGNALS(154),
        SIGNALS_ONLY(155),
        SIGNALS_ONLY_REDUNDANTLY(156),
        SIGNALS_REDUNDANTLY(157),
        SPEC_BIGINT_MATH(158),
        SPEC_JAVA_MATH(159),
        SPEC_PACKAGE(160),
        SPEC_PRIVATE(161),
        SPEC_PROTECTED(162),
        SPEC_PUBLIC(163),
        SPEC_SAFE_MATH(164),
        STATIC_INITIALIZER(165),
        STRICTLY_PURE(166),
        SUBTYPE(167),
        SUCH_THAT(168),
        SUM(169),
        TYPE(170),
        UNINITIALIZED(171),
        UNKNOWN_OP(172),
        UNKNOWN_OP_EQ(173),
        UNREACHABLE(174),
        WARN(175),
        WARN_OP(176),
        WHEN(177),
        WHEN_REDUNDANTLY(178),
        WORKING_SPACE_ESC(179),
        WORKING_SPACE(180),
        WORKING_SPACE_REDUNDANTLY(181),
        WRITABLE(182),
        DOTDOT(183),
        JML_LINE_COMMENT(184),
        SINGLE_LINE_COMMENT(185),
        JML_ENTER_MULTILINE_COMMENT(186),
        ENTER_JAVADOC_COMMENT(187),
        ENTER_JML_BLOCK_COMMENT(188),
        ENTER_MULTILINE_COMMENT(189),
        JML_BLOCK_COMMENT(190),
        JAVADOC_COMMENT(191),
        MULTI_LINE_COMMENT(192),
        JML_MULTI_LINE_COMMENT(193),
        COMMENT_CONTENT(194),
        ABSTRACT(195),
        ASSERT(196),
        BOOLEAN(197),
        BREAK(198),
        BYTE(199),
        CASE(200),
        CATCH(201),
        CHAR(202),
        CLASS(203),
        CONST(204),
        CONTINUE(205),
        _DEFAULT(206),
        DO(207),
        DOUBLE(208),
        ELSE(209),
        ENUM(210),
        EXTENDS(211),
        FALSE(212),
        FINAL(213),
        FINALLY(214),
        FLOAT(215),
        FOR(216),
        GOTO(217),
        IF(218),
        IMPLEMENTS(219),
        IMPORT(220),
        INSTANCEOF(221),
        INT(222),
        INTERFACE(223),
        LONG(224),
        NATIVE(225),
        NEW(226),
        NULL(227),
        PACKAGE(228),
        PRIVATE(229),
        PROTECTED(230),
        PUBLIC(231),
        RECORD(232),
        RETURN(233),
        SHORT(234),
        STATIC(235),
        STRICTFP(236),
        SUPER(237),
        SWITCH(238),
        SYNCHRONIZED(239),
        THIS(240),
        THROW(241),
        THROWS(242),
        TRANSIENT(243),
        TRUE(244),
        TRY(245),
        VOID(246),
        VOLATILE(247),
        WHILE(248),
        YIELD(249),
        REQUIRES(250),
        TO(251),
        WITH(252),
        OPEN(253),
        OPENS(254),
        USES(255),
        MODULE(256),
        EXPORTS(257),
        PROVIDES(258),
        TRANSITIVE(259),
        LONG_LITERAL(260),
        INTEGER_LITERAL(261),
        DECIMAL_LITERAL(262),
        HEX_LITERAL(263),
        OCTAL_LITERAL(264),
        BINARY_LITERAL(265),
        FLOATING_POINT_LITERAL(266),
        DECIMAL_FLOATING_POINT_LITERAL(267),
        DECIMAL_EXPONENT(268),
        HEXADECIMAL_FLOATING_POINT_LITERAL(269),
        HEXADECIMAL_EXPONENT(270),
        HEX_DIGITS(271),
        UNICODE_ESCAPE(272),
        CHARACTER_LITERAL(273),
        STRING_LITERAL(274),
        ENTER_TEXT_BLOCK(275),
        TEXT_BLOCK_LITERAL(276),
        TEXT_BLOCK_CONTENT(277),
        JML_IDENTIFIER(278),
        IDENTIFIER(279),
        LETTER(280),
        PART_LETTER(281),
        LPAREN(282),
        RPAREN(283),
        LBRACE(284),
        RBRACE(285),
        LBRACKET(286),
        RBRACKET(287),
        SEMICOLON(288),
        COMMA(289),
        DOT(290),
        ELLIPSIS(291),
        AT(292),
        DOUBLECOLON(293),
        ASSIGN(294),
        LT(295),
        BANG(296),
        TILDE(297),
        HOOK(298),
        COLON(299),
        ARROW(300),
        EQ(301),
        GE(302),
        LE(303),
        NE(304),
        SC_AND(305),
        SC_OR(306),
        INCR(307),
        DECR(308),
        PLUS(309),
        MINUS(310),
        STAR(311),
        SLASH(312),
        BIT_AND(313),
        BIT_OR(314),
        XOR(315),
        REM(316),
        LSHIFT(317),
        PLUSASSIGN(318),
        MINUSASSIGN(319),
        STARASSIGN(320),
        SLASHASSIGN(321),
        ANDASSIGN(322),
        ORASSIGN(323),
        XORASSIGN(324),
        REMASSIGN(325),
        LSHIFTASSIGN(326),
        RSIGNEDSHIFTASSIGN(327),
        RUNSIGNEDSHIFTASSIGN(328),
        RUNSIGNEDSHIFT(329),
        RSIGNEDSHIFT(330),
        GT(331),
        CTRL_Z(332);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch(kind) {
                case 332:
                    return CTRL_Z;
                case 331:
                    return GT;
                case 330:
                    return RSIGNEDSHIFT;
                case 329:
                    return RUNSIGNEDSHIFT;
                case 328:
                    return RUNSIGNEDSHIFTASSIGN;
                case 327:
                    return RSIGNEDSHIFTASSIGN;
                case 326:
                    return LSHIFTASSIGN;
                case 325:
                    return REMASSIGN;
                case 324:
                    return XORASSIGN;
                case 323:
                    return ORASSIGN;
                case 322:
                    return ANDASSIGN;
                case 321:
                    return SLASHASSIGN;
                case 320:
                    return STARASSIGN;
                case 319:
                    return MINUSASSIGN;
                case 318:
                    return PLUSASSIGN;
                case 317:
                    return LSHIFT;
                case 316:
                    return REM;
                case 315:
                    return XOR;
                case 314:
                    return BIT_OR;
                case 313:
                    return BIT_AND;
                case 312:
                    return SLASH;
                case 311:
                    return STAR;
                case 310:
                    return MINUS;
                case 309:
                    return PLUS;
                case 308:
                    return DECR;
                case 307:
                    return INCR;
                case 306:
                    return SC_OR;
                case 305:
                    return SC_AND;
                case 304:
                    return NE;
                case 303:
                    return LE;
                case 302:
                    return GE;
                case 301:
                    return EQ;
                case 300:
                    return ARROW;
                case 299:
                    return COLON;
                case 298:
                    return HOOK;
                case 297:
                    return TILDE;
                case 296:
                    return BANG;
                case 295:
                    return LT;
                case 294:
                    return ASSIGN;
                case 293:
                    return DOUBLECOLON;
                case 292:
                    return AT;
                case 291:
                    return ELLIPSIS;
                case 290:
                    return DOT;
                case 289:
                    return COMMA;
                case 288:
                    return SEMICOLON;
                case 287:
                    return RBRACKET;
                case 286:
                    return LBRACKET;
                case 285:
                    return RBRACE;
                case 284:
                    return LBRACE;
                case 283:
                    return RPAREN;
                case 282:
                    return LPAREN;
                case 281:
                    return PART_LETTER;
                case 280:
                    return LETTER;
                case 279:
                    return IDENTIFIER;
                case 278:
                    return JML_IDENTIFIER;
                case 277:
                    return TEXT_BLOCK_CONTENT;
                case 276:
                    return TEXT_BLOCK_LITERAL;
                case 275:
                    return ENTER_TEXT_BLOCK;
                case 274:
                    return STRING_LITERAL;
                case 273:
                    return CHARACTER_LITERAL;
                case 272:
                    return UNICODE_ESCAPE;
                case 271:
                    return HEX_DIGITS;
                case 270:
                    return HEXADECIMAL_EXPONENT;
                case 269:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 268:
                    return DECIMAL_EXPONENT;
                case 267:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 266:
                    return FLOATING_POINT_LITERAL;
                case 265:
                    return BINARY_LITERAL;
                case 264:
                    return OCTAL_LITERAL;
                case 263:
                    return HEX_LITERAL;
                case 262:
                    return DECIMAL_LITERAL;
                case 261:
                    return INTEGER_LITERAL;
                case 260:
                    return LONG_LITERAL;
                case 259:
                    return TRANSITIVE;
                case 258:
                    return PROVIDES;
                case 257:
                    return EXPORTS;
                case 256:
                    return MODULE;
                case 255:
                    return USES;
                case 254:
                    return OPENS;
                case 253:
                    return OPEN;
                case 252:
                    return WITH;
                case 251:
                    return TO;
                case 250:
                    return REQUIRES;
                case 249:
                    return YIELD;
                case 248:
                    return WHILE;
                case 247:
                    return VOLATILE;
                case 246:
                    return VOID;
                case 245:
                    return TRY;
                case 244:
                    return TRUE;
                case 243:
                    return TRANSIENT;
                case 242:
                    return THROWS;
                case 241:
                    return THROW;
                case 240:
                    return THIS;
                case 239:
                    return SYNCHRONIZED;
                case 238:
                    return SWITCH;
                case 237:
                    return SUPER;
                case 236:
                    return STRICTFP;
                case 235:
                    return STATIC;
                case 234:
                    return SHORT;
                case 233:
                    return RETURN;
                case 232:
                    return RECORD;
                case 231:
                    return PUBLIC;
                case 230:
                    return PROTECTED;
                case 229:
                    return PRIVATE;
                case 228:
                    return PACKAGE;
                case 227:
                    return NULL;
                case 226:
                    return NEW;
                case 225:
                    return NATIVE;
                case 224:
                    return LONG;
                case 223:
                    return INTERFACE;
                case 222:
                    return INT;
                case 221:
                    return INSTANCEOF;
                case 220:
                    return IMPORT;
                case 219:
                    return IMPLEMENTS;
                case 218:
                    return IF;
                case 217:
                    return GOTO;
                case 216:
                    return FOR;
                case 215:
                    return FLOAT;
                case 214:
                    return FINALLY;
                case 213:
                    return FINAL;
                case 212:
                    return FALSE;
                case 211:
                    return EXTENDS;
                case 210:
                    return ENUM;
                case 209:
                    return ELSE;
                case 208:
                    return DOUBLE;
                case 207:
                    return DO;
                case 206:
                    return _DEFAULT;
                case 205:
                    return CONTINUE;
                case 204:
                    return CONST;
                case 203:
                    return CLASS;
                case 202:
                    return CHAR;
                case 201:
                    return CATCH;
                case 200:
                    return CASE;
                case 199:
                    return BYTE;
                case 198:
                    return BREAK;
                case 197:
                    return BOOLEAN;
                case 196:
                    return ASSERT;
                case 195:
                    return ABSTRACT;
                case 194:
                    return COMMENT_CONTENT;
                case 193:
                    return JML_MULTI_LINE_COMMENT;
                case 192:
                    return MULTI_LINE_COMMENT;
                case 191:
                    return JAVADOC_COMMENT;
                case 190:
                    return JML_BLOCK_COMMENT;
                case 189:
                    return ENTER_MULTILINE_COMMENT;
                case 188:
                    return ENTER_JML_BLOCK_COMMENT;
                case 187:
                    return ENTER_JAVADOC_COMMENT;
                case 186:
                    return JML_ENTER_MULTILINE_COMMENT;
                case 185:
                    return SINGLE_LINE_COMMENT;
                case 184:
                    return JML_LINE_COMMENT;
                case 183:
                    return DOTDOT;
                case 182:
                    return WRITABLE;
                case 181:
                    return WORKING_SPACE_REDUNDANTLY;
                case 180:
                    return WORKING_SPACE;
                case 179:
                    return WORKING_SPACE_ESC;
                case 178:
                    return WHEN_REDUNDANTLY;
                case 177:
                    return WHEN;
                case 176:
                    return WARN_OP;
                case 175:
                    return WARN;
                case 174:
                    return UNREACHABLE;
                case 173:
                    return UNKNOWN_OP_EQ;
                case 172:
                    return UNKNOWN_OP;
                case 171:
                    return UNINITIALIZED;
                case 170:
                    return TYPE;
                case 169:
                    return SUM;
                case 168:
                    return SUCH_THAT;
                case 167:
                    return SUBTYPE;
                case 166:
                    return STRICTLY_PURE;
                case 165:
                    return STATIC_INITIALIZER;
                case 164:
                    return SPEC_SAFE_MATH;
                case 163:
                    return SPEC_PUBLIC;
                case 162:
                    return SPEC_PROTECTED;
                case 161:
                    return SPEC_PRIVATE;
                case 160:
                    return SPEC_PACKAGE;
                case 159:
                    return SPEC_JAVA_MATH;
                case 158:
                    return SPEC_BIGINT_MATH;
                case 157:
                    return SIGNALS_REDUNDANTLY;
                case 156:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 155:
                    return SIGNALS_ONLY;
                case 154:
                    return SIGNALS;
                case 153:
                    return SET;
                case 152:
                    return SAFE_MATH;
                case 151:
                    return RETURN_BEHAVIOUR;
                case 150:
                    return BACKARROW;
                case 149:
                    return RETURN_BEHAVIOR;
                case 148:
                    return RETURNS_REDUNDANTLY;
                case 147:
                    return RETURNS;
                case 146:
                    return RESULT;
                case 145:
                    return REQUIRES_REDUNDANTLY;
                case 144:
                    return REPRESENTS_REDUNDANTLY;
                case 143:
                    return REPRESENTS;
                case 142:
                    return REFINING;
                case 141:
                    return READABLE;
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
                    return FEASIBLE_BEHAVIOUR;
                case 124:
                    return FEASIBLE_BEHAVIOR;
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
                    return MODIFIES_REDUNDANTLY;
                case 113:
                    return MODIFIES;
                case 112:
                    return LOOP_MODIFIES;
                case 111:
                    return MODIFIABLE_REDUNDANTLY;
                case 110:
                    return MODIFIABLE;
                case 109:
                    return MODEL_PROGRAM;
                case 108:
                    return MODEL;
                case 107:
                    return MIN;
                case 106:
                    return METHOD;
                case 105:
                    return MEASURED_BY_REDUNDANTLY;
                case 104:
                    return ESC_MEASURED_BY;
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
                    return LOOP_INVARIANT_FREE;
                case 95:
                    return LOOP_INVARIANT;
                case 94:
                    return LOOP_CONTRACT;
                case 93:
                    return LBL;
                case 92:
                    return LBLPOS;
                case 91:
                    return LBLNEG;
                case 90:
                    return JAVA_MATH;
                case 89:
                    return IN_REDUNDANTLY;
                case 88:
                    return INVARIANT_REDUNDANTLY;
                case 87:
                    return NON_NULL_BY_DEFAULT;
                case 86:
                    return NO_STATE;
                case 85:
                    return TWO_STATE;
                case 84:
                    return INSTANCE;
                case 83:
                    return INITIALLY;
                case 82:
                    return INITIALIZER;
                case 81:
                    return IN;
                case 80:
                    return IMPLIES_THAT;
                case 79:
                    return HENCE_BY_REDUNDANTLY;
                case 78:
                    return HENCE_BY;
                case 77:
                    return HELPER;
                case 76:
                    return GHOST;
                case 75:
                    return FOR_EXAMPLE;
                case 74:
                    return FORALL;
                case 73:
                    return LET;
                case 72:
                    return FORALLQ;
                case 71:
                    return FIELD;
                case 70:
                    return EXTRACT;
                case 69:
                    return EXSURES_REDUNDANTLY;
                case 68:
                    return EXSURES;
                case 67:
                    return EXISTS;
                case 66:
                    return EXCEPTIONAL_EXAMPLE;
                case 65:
                    return EXCEPTIONAL_BEHAVIOUR;
                case 64:
                    return EXCEPTIONAL_BEHAVIOR;
                case 63:
                    return EXAMPLE;
                case 62:
                    return ERASES;
                case 61:
                    return IMPLICATION_BACKWARD;
                case 60:
                    return IMPLICATION;
                case 59:
                    return EQUIVALENCE;
                case 58:
                    return REQUIRES_FREE;
                case 57:
                    return ENSURES_FREE;
                case 56:
                    return ENSURES_REDUNDANTLY;
                case 55:
                    return ENSURES;
                case 54:
                    return DURATION_REDUNDANTLY;
                case 53:
                    return DURATION;
                case 52:
                    return DIVERGES_REDUNDANTLY;
                case 51:
                    return DIVERGES;
                case 50:
                    return DETERMINES;
                case 49:
                    return DECREASING_REDUNDANTLY;
                case 48:
                    return DECREASING;
                case 47:
                    return DECREASES_REDUNDANTLY;
                case 46:
                    return DECREASES;
                case 45:
                    return DECLASSIFIES;
                case 44:
                    return CONTINUE_BEHAVIOUR;
                case 43:
                    return CONTINUE_BEHAVIOR;
                case 42:
                    return CONTINUES_REDUNDANTLY;
                case 41:
                    return CONTINUES;
                case 40:
                    return CONSTRUCTOR;
                case 39:
                    return CONSTRAINT_REDUNDANTLY;
                case 38:
                    return CONSTRAINT;
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
