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
        LOOP_CONTRACT(99),
        LOOP_INVARIANT(100),
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
        MODIFIES(116),
        MODIFIES_REDUNDANTLY(117),
        MONITORED(118),
        MONITORS_FOR(119),
        NESTED_CONTRACT_END(120),
        NESTED_CONTRACT_START(121),
        NEW_OBJECT(122),
        NONNULLELEMENTS(123),
        NON_NULL(124),
        NORMAL_BEHAVIOR(125),
        NORMAL_BEHAVIOUR(126),
        NORMAL_EXAMPLE(127),
        NOWARN(128),
        NOWARN_OP(129),
        NULLABLE(130),
        NULLABLE_BY_DEFAULT(131),
        NUM_OF(132),
        OLD(133),
        OR(134),
        POST(135),
        POST_REDUNDANTLY(136),
        PRE_ESC(137),
        PRE(138),
        PRE_REDUNDANTLY(139),
        PRODUCT(140),
        PURE(141),
        REACH(142),
        READABLE(143),
        REAL(144),
        REFINING(145),
        REPRESENTS(146),
        REPRESENTS_REDUNDANTLY(147),
        REQUIRES_REDUNDANTLY(148),
        RESULT(149),
        RETURNS(150),
        RETURNS_REDUNDANTLY(151),
        RETURN_BEHAVIOR(152),
        RETURN_BEHAVIOUR(153),
        SAFE_MATH(154),
        SET(155),
        SIGNALS(156),
        SIGNALS_ONLY(157),
        SIGNALS_ONLY_REDUNDANTLY(158),
        SIGNALS_REDUNDANTLY(159),
        SPEC_BIGINT_MATH(160),
        SPEC_JAVA_MATH(161),
        SPEC_PACKAGE(162),
        SPEC_PRIVATE(163),
        SPEC_PROTECTED(164),
        SPEC_PUBLIC(165),
        SPEC_SAFE_MATH(166),
        STATIC_INITIALIZER(167),
        STRICTLY_PURE(168),
        SUBTYPE(169),
        SUCH_THAT(170),
        SUM(171),
        TYPE(172),
        TYPEOF(173),
        UNINITIALIZED(174),
        UNKNOWN_OP(175),
        UNKNOWN_OP_EQ(176),
        UNREACHABLE(177),
        WARN(178),
        WARN_OP(179),
        WHEN(180),
        WHEN_REDUNDANTLY(181),
        WORKING_SPACE_ESC(182),
        WORKING_SPACE(183),
        WORKING_SPACE_REDUNDANTLY(184),
        WRITABLE(185),
        ENTER_JAVADOC_COMMENT(186),
        ENTER_MULTILINE_COMMENT(187),
        JAVADOC_COMMENT(188),
        MULTI_LINE_COMMENT(189),
        COMMENT_CONTENT(190),
        ABSTRACT(191),
        ASSERT(192),
        BOOLEAN(193),
        BREAK(194),
        BYTE(195),
        CASE(196),
        CATCH(197),
        CHAR(198),
        CLASS(199),
        CONST(200),
        CONTINUE(201),
        _DEFAULT(202),
        DO(203),
        DOUBLE(204),
        ELSE(205),
        ENUM(206),
        EXTENDS(207),
        FALSE(208),
        FINAL(209),
        FINALLY(210),
        FLOAT(211),
        FOR(212),
        GOTO(213),
        IF(214),
        IMPLEMENTS(215),
        IMPORT(216),
        INSTANCEOF(217),
        INT(218),
        INTERFACE(219),
        LONG(220),
        NATIVE(221),
        NEW(222),
        NULL(223),
        PACKAGE(224),
        PRIVATE(225),
        PROTECTED(226),
        PUBLIC(227),
        RECORD(228),
        RETURN(229),
        SHORT(230),
        STATIC(231),
        STRICTFP(232),
        SUPER(233),
        SWITCH(234),
        SYNCHRONIZED(235),
        THIS(236),
        THROW(237),
        THROWS(238),
        TRANSIENT(239),
        TRUE(240),
        TRY(241),
        VOID(242),
        VOLATILE(243),
        WHILE(244),
        YIELD(245),
        REQUIRES(246),
        TO(247),
        WITH(248),
        OPEN(249),
        OPENS(250),
        USES(251),
        MODULE(252),
        EXPORTS(253),
        PROVIDES(254),
        TRANSITIVE(255),
        LONG_LITERAL(256),
        INTEGER_LITERAL(257),
        DECIMAL_LITERAL(258),
        HEX_LITERAL(259),
        OCTAL_LITERAL(260),
        BINARY_LITERAL(261),
        FLOATING_POINT_LITERAL(262),
        DECIMAL_FLOATING_POINT_LITERAL(263),
        DECIMAL_EXPONENT(264),
        HEXADECIMAL_FLOATING_POINT_LITERAL(265),
        HEXADECIMAL_EXPONENT(266),
        HEX_DIGITS(267),
        UNICODE_ESCAPE(268),
        CHARACTER_LITERAL(269),
        STRING_LITERAL(270),
        ENTER_TEXT_BLOCK(271),
        TEXT_BLOCK_LITERAL(272),
        TEXT_BLOCK_CONTENT(273),
        JML_IDENTIFIER(274),
        IDENTIFIER(275),
        LETTER(276),
        PART_LETTER(277),
        LPAREN(278),
        RPAREN(279),
        LBRACE(280),
        RBRACE(281),
        LBRACKET(282),
        RBRACKET(283),
        SEMICOLON(284),
        COMMA(285),
        DOT(286),
        ELLIPSIS(287),
        AT(288),
        DOUBLECOLON(289),
        ASSIGN(290),
        LT(291),
        BANG(292),
        TILDE(293),
        HOOK(294),
        COLON(295),
        ARROW(296),
        EQ(297),
        GE(298),
        LE(299),
        NE(300),
        SC_AND(301),
        SC_OR(302),
        INCR(303),
        DECR(304),
        PLUS(305),
        MINUS(306),
        STAR(307),
        SLASH(308),
        BIT_AND(309),
        BIT_OR(310),
        XOR(311),
        REM(312),
        LSHIFT(313),
        PLUSASSIGN(314),
        MINUSASSIGN(315),
        STARASSIGN(316),
        SLASHASSIGN(317),
        ANDASSIGN(318),
        ORASSIGN(319),
        XORASSIGN(320),
        REMASSIGN(321),
        LSHIFTASSIGN(322),
        RSIGNEDSHIFTASSIGN(323),
        RUNSIGNEDSHIFTASSIGN(324),
        RUNSIGNEDSHIFT(325),
        RSIGNEDSHIFT(326),
        GT(327),
        CTRL_Z(328);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 328:
                    return CTRL_Z;
                case 327:
                    return GT;
                case 326:
                    return RSIGNEDSHIFT;
                case 325:
                    return RUNSIGNEDSHIFT;
                case 324:
                    return RUNSIGNEDSHIFTASSIGN;
                case 323:
                    return RSIGNEDSHIFTASSIGN;
                case 322:
                    return LSHIFTASSIGN;
                case 321:
                    return REMASSIGN;
                case 320:
                    return XORASSIGN;
                case 319:
                    return ORASSIGN;
                case 318:
                    return ANDASSIGN;
                case 317:
                    return SLASHASSIGN;
                case 316:
                    return STARASSIGN;
                case 315:
                    return MINUSASSIGN;
                case 314:
                    return PLUSASSIGN;
                case 313:
                    return LSHIFT;
                case 312:
                    return REM;
                case 311:
                    return XOR;
                case 310:
                    return BIT_OR;
                case 309:
                    return BIT_AND;
                case 308:
                    return SLASH;
                case 307:
                    return STAR;
                case 306:
                    return MINUS;
                case 305:
                    return PLUS;
                case 304:
                    return DECR;
                case 303:
                    return INCR;
                case 302:
                    return SC_OR;
                case 301:
                    return SC_AND;
                case 300:
                    return NE;
                case 299:
                    return LE;
                case 298:
                    return GE;
                case 297:
                    return EQ;
                case 296:
                    return ARROW;
                case 295:
                    return COLON;
                case 294:
                    return HOOK;
                case 293:
                    return TILDE;
                case 292:
                    return BANG;
                case 291:
                    return LT;
                case 290:
                    return ASSIGN;
                case 289:
                    return DOUBLECOLON;
                case 288:
                    return AT;
                case 287:
                    return ELLIPSIS;
                case 286:
                    return DOT;
                case 285:
                    return COMMA;
                case 284:
                    return SEMICOLON;
                case 283:
                    return RBRACKET;
                case 282:
                    return LBRACKET;
                case 281:
                    return RBRACE;
                case 280:
                    return LBRACE;
                case 279:
                    return RPAREN;
                case 278:
                    return LPAREN;
                case 277:
                    return PART_LETTER;
                case 276:
                    return LETTER;
                case 275:
                    return IDENTIFIER;
                case 274:
                    return JML_IDENTIFIER;
                case 273:
                    return TEXT_BLOCK_CONTENT;
                case 272:
                    return TEXT_BLOCK_LITERAL;
                case 271:
                    return ENTER_TEXT_BLOCK;
                case 270:
                    return STRING_LITERAL;
                case 269:
                    return CHARACTER_LITERAL;
                case 268:
                    return UNICODE_ESCAPE;
                case 267:
                    return HEX_DIGITS;
                case 266:
                    return HEXADECIMAL_EXPONENT;
                case 265:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 264:
                    return DECIMAL_EXPONENT;
                case 263:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 262:
                    return FLOATING_POINT_LITERAL;
                case 261:
                    return BINARY_LITERAL;
                case 260:
                    return OCTAL_LITERAL;
                case 259:
                    return HEX_LITERAL;
                case 258:
                    return DECIMAL_LITERAL;
                case 257:
                    return INTEGER_LITERAL;
                case 256:
                    return LONG_LITERAL;
                case 255:
                    return TRANSITIVE;
                case 254:
                    return PROVIDES;
                case 253:
                    return EXPORTS;
                case 252:
                    return MODULE;
                case 251:
                    return USES;
                case 250:
                    return OPENS;
                case 249:
                    return OPEN;
                case 248:
                    return WITH;
                case 247:
                    return TO;
                case 246:
                    return REQUIRES;
                case 245:
                    return YIELD;
                case 244:
                    return WHILE;
                case 243:
                    return VOLATILE;
                case 242:
                    return VOID;
                case 241:
                    return TRY;
                case 240:
                    return TRUE;
                case 239:
                    return TRANSIENT;
                case 238:
                    return THROWS;
                case 237:
                    return THROW;
                case 236:
                    return THIS;
                case 235:
                    return SYNCHRONIZED;
                case 234:
                    return SWITCH;
                case 233:
                    return SUPER;
                case 232:
                    return STRICTFP;
                case 231:
                    return STATIC;
                case 230:
                    return SHORT;
                case 229:
                    return RETURN;
                case 228:
                    return RECORD;
                case 227:
                    return PUBLIC;
                case 226:
                    return PROTECTED;
                case 225:
                    return PRIVATE;
                case 224:
                    return PACKAGE;
                case 223:
                    return NULL;
                case 222:
                    return NEW;
                case 221:
                    return NATIVE;
                case 220:
                    return LONG;
                case 219:
                    return INTERFACE;
                case 218:
                    return INT;
                case 217:
                    return INSTANCEOF;
                case 216:
                    return IMPORT;
                case 215:
                    return IMPLEMENTS;
                case 214:
                    return IF;
                case 213:
                    return GOTO;
                case 212:
                    return FOR;
                case 211:
                    return FLOAT;
                case 210:
                    return FINALLY;
                case 209:
                    return FINAL;
                case 208:
                    return FALSE;
                case 207:
                    return EXTENDS;
                case 206:
                    return ENUM;
                case 205:
                    return ELSE;
                case 204:
                    return DOUBLE;
                case 203:
                    return DO;
                case 202:
                    return _DEFAULT;
                case 201:
                    return CONTINUE;
                case 200:
                    return CONST;
                case 199:
                    return CLASS;
                case 198:
                    return CHAR;
                case 197:
                    return CATCH;
                case 196:
                    return CASE;
                case 195:
                    return BYTE;
                case 194:
                    return BREAK;
                case 193:
                    return BOOLEAN;
                case 192:
                    return ASSERT;
                case 191:
                    return ABSTRACT;
                case 190:
                    return COMMENT_CONTENT;
                case 189:
                    return MULTI_LINE_COMMENT;
                case 188:
                    return JAVADOC_COMMENT;
                case 187:
                    return ENTER_MULTILINE_COMMENT;
                case 186:
                    return ENTER_JAVADOC_COMMENT;
                case 185:
                    return WRITABLE;
                case 184:
                    return WORKING_SPACE_REDUNDANTLY;
                case 183:
                    return WORKING_SPACE;
                case 182:
                    return WORKING_SPACE_ESC;
                case 181:
                    return WHEN_REDUNDANTLY;
                case 180:
                    return WHEN;
                case 179:
                    return WARN_OP;
                case 178:
                    return WARN;
                case 177:
                    return UNREACHABLE;
                case 176:
                    return UNKNOWN_OP_EQ;
                case 175:
                    return UNKNOWN_OP;
                case 174:
                    return UNINITIALIZED;
                case 173:
                    return TYPEOF;
                case 172:
                    return TYPE;
                case 171:
                    return SUM;
                case 170:
                    return SUCH_THAT;
                case 169:
                    return SUBTYPE;
                case 168:
                    return STRICTLY_PURE;
                case 167:
                    return STATIC_INITIALIZER;
                case 166:
                    return SPEC_SAFE_MATH;
                case 165:
                    return SPEC_PUBLIC;
                case 164:
                    return SPEC_PROTECTED;
                case 163:
                    return SPEC_PRIVATE;
                case 162:
                    return SPEC_PACKAGE;
                case 161:
                    return SPEC_JAVA_MATH;
                case 160:
                    return SPEC_BIGINT_MATH;
                case 159:
                    return SIGNALS_REDUNDANTLY;
                case 158:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 157:
                    return SIGNALS_ONLY;
                case 156:
                    return SIGNALS;
                case 155:
                    return SET;
                case 154:
                    return SAFE_MATH;
                case 153:
                    return RETURN_BEHAVIOUR;
                case 152:
                    return RETURN_BEHAVIOR;
                case 151:
                    return RETURNS_REDUNDANTLY;
                case 150:
                    return RETURNS;
                case 149:
                    return RESULT;
                case 148:
                    return REQUIRES_REDUNDANTLY;
                case 147:
                    return REPRESENTS_REDUNDANTLY;
                case 146:
                    return REPRESENTS;
                case 145:
                    return REFINING;
                case 144:
                    return REAL;
                case 143:
                    return READABLE;
                case 142:
                    return REACH;
                case 141:
                    return PURE;
                case 140:
                    return PRODUCT;
                case 139:
                    return PRE_REDUNDANTLY;
                case 138:
                    return PRE;
                case 137:
                    return PRE_ESC;
                case 136:
                    return POST_REDUNDANTLY;
                case 135:
                    return POST;
                case 134:
                    return OR;
                case 133:
                    return OLD;
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
                    return NORMAL_EXAMPLE;
                case 126:
                    return NORMAL_BEHAVIOUR;
                case 125:
                    return NORMAL_BEHAVIOR;
                case 124:
                    return NON_NULL;
                case 123:
                    return NONNULLELEMENTS;
                case 122:
                    return NEW_OBJECT;
                case 121:
                    return NESTED_CONTRACT_START;
                case 120:
                    return NESTED_CONTRACT_END;
                case 119:
                    return MONITORS_FOR;
                case 118:
                    return MONITORED;
                case 117:
                    return MODIFIES_REDUNDANTLY;
                case 116:
                    return MODIFIES;
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
                    return LOOP_INVARIANT;
                case 99:
                    return LOOP_CONTRACT;
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
