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
        JML_IGNORE_SINGLE_LINE_START(2),
        SPACE(3),
        WINDOWS_EOL(4),
        UNIX_EOL(5),
        OLD_MAC_EOL(6),
        INVARIANT(7),
        ABRUPT_BEHAVIOR(8),
        ABRUPT_BEHAVIOUR(9),
        MODEL_BEHAVIOR(10),
        MODEL_BEHAVIOUR(11),
        ACCESSIBLE(12),
        ACCESSIBLE_REDUNDANTLY(13),
        ALSO(14),
        ANTIVALENCE(15),
        ASSERT_REDUNDANTLY(16),
        ASSIGNABLE(17),
        ASSIGNABLE_REDUNDANTLY(18),
        ASSUME(19),
        ASSUME_REDUNDANTLY(20),
        AXIOM(21),
        BEHAVIOR(22),
        BEHAVIOUR(23),
        BIGINT(24),
        BIGINT_MATH(25),
        BREAKS(26),
        BREAKS_REDUNDANTLY(27),
        BREAK_BEHAVIOR(28),
        BREAK_BEHAVIOUR(29),
        CALLABLE(30),
        CALLABLE_REDUNDANTLY(31),
        CAPTURES(32),
        CAPTURES_REDUNDANTLY(33),
        CHOOSE(34),
        CHOOSE_IF(35),
        CODE(36),
        CODE_BIGINT_MATH(37),
        CODE_JAVA_MATH(38),
        CODE_SAFE_MATH(39),
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
        DIVERGES(53),
        DIVERGES_REDUNDANTLY(54),
        DURATION(55),
        DURATION_REDUNDANTLY(56),
        ELEMTYPE(57),
        ENSURES(58),
        ENSURES_REDUNDANTLY(59),
        ENSURES_FREE(60),
        REQUIRES_FREE(61),
        EQUIVALENCE(62),
        IMPLICATION(63),
        IMPLICATION_BACKWARD(64),
        ERASES(65),
        EXAMPLE(66),
        EXCEPTIONAL_BEHAVIOR(67),
        EXCEPTIONAL_BEHAVIOUR(68),
        EXCEPTIONAL_EXAMPLE(69),
        EXISTS(70),
        EXSURES(71),
        EXSURES_REDUNDANTLY(72),
        EXTRACT(73),
        FIELD(74),
        FORALLQ(75),
        FORALL(76),
        FOR_EXAMPLE(77),
        GHOST(78),
        HELPER(79),
        HENCE_BY(80),
        HENCE_BY_REDUNDANTLY(81),
        IMPLIES_THAT(82),
        IN(83),
        INITIALIZER(84),
        INITIALLY(85),
        INSTANCE(86),
        TWO_STATE(87),
        NO_STATE(88),
        NON_NULL_BY_DEFAULT(89),
        INVARIANT_REDUNDANTLY(90),
        IN_REDUNDANTLY(91),
        JAVA_MATH(92),
        LOOP_CONTRACT(93),
        LOOP_INVARIANT(94),
        LOOP_INVARIANT_FREE(95),
        LOOP_INVARIANT_REDUNDANTLY(96),
        MAINTAINING(97),
        MAINTAINING_REDUNDANTLY(98),
        MAPS(99),
        MAPS_REDUNDANTLY(100),
        MAX(101),
        MEASURED_BY(102),
        ESC_MEASURED_BY(103),
        MEASURED_BY_REDUNDANTLY(104),
        METHOD(105),
        MIN(106),
        MODEL(107),
        MODEL_PROGRAM(108),
        MODIFIABLE(109),
        MODIFIABLE_REDUNDANTLY(110),
        LOOP_MODIFIES(111),
        MODIFIES(112),
        MODIFIES_REDUNDANTLY(113),
        MONITORED(114),
        MONITORS_FOR(115),
        NESTED_CONTRACT_END(116),
        NESTED_CONTRACT_START(117),
        NEW_OBJECT(118),
        NONNULLELEMENTS(119),
        NON_NULL(120),
        NORMAL_BEHAVIOR(121),
        NORMAL_BEHAVIOUR(122),
        NORMAL_EXAMPLE(123),
        NOWARN(124),
        NOWARN_OP(125),
        NULLABLE(126),
        NULLABLE_BY_DEFAULT(127),
        NUM_OF(128),
        OLD(129),
        OR(130),
        POST(131),
        POST_REDUNDANTLY(132),
        PRE_ESC(133),
        PRE(134),
        PRE_REDUNDANTLY(135),
        PRODUCT(136),
        PURE(137),
        READABLE(138),
        REFINING(139),
        REPRESENTS(140),
        REPRESENTS_REDUNDANTLY(141),
        REQUIRES_REDUNDANTLY(142),
        RESULT(143),
        RETURNS(144),
        RETURNS_REDUNDANTLY(145),
        RETURN_BEHAVIOR(146),
        RETURN_BEHAVIOUR(147),
        SAFE_MATH(148),
        SET(149),
        SIGNALS(150),
        SIGNALS_ONLY(151),
        SIGNALS_ONLY_REDUNDANTLY(152),
        SIGNALS_REDUNDANTLY(153),
        SPEC_BIGINT_MATH(154),
        SPEC_JAVA_MATH(155),
        SPEC_PACKAGE(156),
        SPEC_PRIVATE(157),
        SPEC_PROTECTED(158),
        SPEC_PUBLIC(159),
        SPEC_SAFE_MATH(160),
        STATIC_INITIALIZER(161),
        STRICTLY_PURE(162),
        SUBTYPE(163),
        SUCH_THAT(164),
        SUM(165),
        TYPE(166),
        UNINITIALIZED(167),
        UNKNOWN_OP(168),
        UNKNOWN_OP_EQ(169),
        UNREACHABLE(170),
        WARN(171),
        WARN_OP(172),
        WHEN(173),
        WHEN_REDUNDANTLY(174),
        WORKING_SPACE_ESC(175),
        WORKING_SPACE(176),
        WORKING_SPACE_REDUNDANTLY(177),
        WRITABLE(178),
        DOTDOT(179),
        JML_LINE_COMMENT(180),
        SINGLE_LINE_COMMENT(181),
        ENTER_JAVADOC_COMMENT(182),
        ENTER_JML_BLOCK_COMMENT(183),
        ENTER_MULTILINE_COMMENT(184),
        JML_BLOCK_COMMENT(185),
        JAVADOC_COMMENT(186),
        MULTI_LINE_COMMENT(187),
        COMMENT_CONTENT(188),
        ABSTRACT(189),
        ASSERT(190),
        BOOLEAN(191),
        BREAK(192),
        BYTE(193),
        CASE(194),
        CATCH(195),
        CHAR(196),
        CLASS(197),
        CONST(198),
        CONTINUE(199),
        _DEFAULT(200),
        DO(201),
        DOUBLE(202),
        ELSE(203),
        ENUM(204),
        EXTENDS(205),
        FALSE(206),
        FINAL(207),
        FINALLY(208),
        FLOAT(209),
        FOR(210),
        GOTO(211),
        IF(212),
        IMPLEMENTS(213),
        IMPORT(214),
        INSTANCEOF(215),
        INT(216),
        INTERFACE(217),
        LONG(218),
        NATIVE(219),
        NEW(220),
        NULL(221),
        PACKAGE(222),
        PRIVATE(223),
        PROTECTED(224),
        PUBLIC(225),
        RECORD(226),
        RETURN(227),
        SHORT(228),
        STATIC(229),
        STRICTFP(230),
        SUPER(231),
        SWITCH(232),
        SYNCHRONIZED(233),
        THIS(234),
        THROW(235),
        THROWS(236),
        TRANSIENT(237),
        TRUE(238),
        TRY(239),
        VOID(240),
        VOLATILE(241),
        WHILE(242),
        YIELD(243),
        REQUIRES(244),
        TO(245),
        WITH(246),
        OPEN(247),
        OPENS(248),
        USES(249),
        MODULE(250),
        EXPORTS(251),
        PROVIDES(252),
        TRANSITIVE(253),
        LONG_LITERAL(254),
        INTEGER_LITERAL(255),
        DECIMAL_LITERAL(256),
        HEX_LITERAL(257),
        OCTAL_LITERAL(258),
        BINARY_LITERAL(259),
        FLOATING_POINT_LITERAL(260),
        DECIMAL_FLOATING_POINT_LITERAL(261),
        DECIMAL_EXPONENT(262),
        HEXADECIMAL_FLOATING_POINT_LITERAL(263),
        HEXADECIMAL_EXPONENT(264),
        HEX_DIGITS(265),
        UNICODE_ESCAPE(266),
        CHARACTER_LITERAL(267),
        STRING_LITERAL(268),
        ENTER_TEXT_BLOCK(269),
        TEXT_BLOCK_LITERAL(270),
        TEXT_BLOCK_CONTENT(271),
        JML_IDENTIFIER(272),
        IDENTIFIER(273),
        LETTER(274),
        PART_LETTER(275),
        LPAREN(276),
        RPAREN(277),
        LBRACE(278),
        RBRACE(279),
        LBRACKET(280),
        RBRACKET(281),
        SEMICOLON(282),
        COMMA(283),
        DOT(284),
        ELLIPSIS(285),
        AT(286),
        DOUBLECOLON(287),
        ASSIGN(288),
        LT(289),
        BANG(290),
        TILDE(291),
        HOOK(292),
        COLON(293),
        ARROW(294),
        EQ(295),
        GE(296),
        LE(297),
        NE(298),
        SC_AND(299),
        SC_OR(300),
        INCR(301),
        DECR(302),
        PLUS(303),
        MINUS(304),
        STAR(305),
        SLASH(306),
        BIT_AND(307),
        BIT_OR(308),
        XOR(309),
        REM(310),
        LSHIFT(311),
        PLUSASSIGN(312),
        MINUSASSIGN(313),
        STARASSIGN(314),
        SLASHASSIGN(315),
        ANDASSIGN(316),
        ORASSIGN(317),
        XORASSIGN(318),
        REMASSIGN(319),
        LSHIFTASSIGN(320),
        RSIGNEDSHIFTASSIGN(321),
        RUNSIGNEDSHIFTASSIGN(322),
        RUNSIGNEDSHIFT(323),
        RSIGNEDSHIFT(324),
        GT(325),
        CTRL_Z(326);

        private final int kind;

        Kind(int kind) {
            this.kind = kind;
        }

        public static Kind valueOf(int kind) {
            switch (kind) {
                case 326:
                    return CTRL_Z;
                case 325:
                    return GT;
                case 324:
                    return RSIGNEDSHIFT;
                case 323:
                    return RUNSIGNEDSHIFT;
                case 322:
                    return RUNSIGNEDSHIFTASSIGN;
                case 321:
                    return RSIGNEDSHIFTASSIGN;
                case 320:
                    return LSHIFTASSIGN;
                case 319:
                    return REMASSIGN;
                case 318:
                    return XORASSIGN;
                case 317:
                    return ORASSIGN;
                case 316:
                    return ANDASSIGN;
                case 315:
                    return SLASHASSIGN;
                case 314:
                    return STARASSIGN;
                case 313:
                    return MINUSASSIGN;
                case 312:
                    return PLUSASSIGN;
                case 311:
                    return LSHIFT;
                case 310:
                    return REM;
                case 309:
                    return XOR;
                case 308:
                    return BIT_OR;
                case 307:
                    return BIT_AND;
                case 306:
                    return SLASH;
                case 305:
                    return STAR;
                case 304:
                    return MINUS;
                case 303:
                    return PLUS;
                case 302:
                    return DECR;
                case 301:
                    return INCR;
                case 300:
                    return SC_OR;
                case 299:
                    return SC_AND;
                case 298:
                    return NE;
                case 297:
                    return LE;
                case 296:
                    return GE;
                case 295:
                    return EQ;
                case 294:
                    return ARROW;
                case 293:
                    return COLON;
                case 292:
                    return HOOK;
                case 291:
                    return TILDE;
                case 290:
                    return BANG;
                case 289:
                    return LT;
                case 288:
                    return ASSIGN;
                case 287:
                    return DOUBLECOLON;
                case 286:
                    return AT;
                case 285:
                    return ELLIPSIS;
                case 284:
                    return DOT;
                case 283:
                    return COMMA;
                case 282:
                    return SEMICOLON;
                case 281:
                    return RBRACKET;
                case 280:
                    return LBRACKET;
                case 279:
                    return RBRACE;
                case 278:
                    return LBRACE;
                case 277:
                    return RPAREN;
                case 276:
                    return LPAREN;
                case 275:
                    return PART_LETTER;
                case 274:
                    return LETTER;
                case 273:
                    return IDENTIFIER;
                case 272:
                    return JML_IDENTIFIER;
                case 271:
                    return TEXT_BLOCK_CONTENT;
                case 270:
                    return TEXT_BLOCK_LITERAL;
                case 269:
                    return ENTER_TEXT_BLOCK;
                case 268:
                    return STRING_LITERAL;
                case 267:
                    return CHARACTER_LITERAL;
                case 266:
                    return UNICODE_ESCAPE;
                case 265:
                    return HEX_DIGITS;
                case 264:
                    return HEXADECIMAL_EXPONENT;
                case 263:
                    return HEXADECIMAL_FLOATING_POINT_LITERAL;
                case 262:
                    return DECIMAL_EXPONENT;
                case 261:
                    return DECIMAL_FLOATING_POINT_LITERAL;
                case 260:
                    return FLOATING_POINT_LITERAL;
                case 259:
                    return BINARY_LITERAL;
                case 258:
                    return OCTAL_LITERAL;
                case 257:
                    return HEX_LITERAL;
                case 256:
                    return DECIMAL_LITERAL;
                case 255:
                    return INTEGER_LITERAL;
                case 254:
                    return LONG_LITERAL;
                case 253:
                    return TRANSITIVE;
                case 252:
                    return PROVIDES;
                case 251:
                    return EXPORTS;
                case 250:
                    return MODULE;
                case 249:
                    return USES;
                case 248:
                    return OPENS;
                case 247:
                    return OPEN;
                case 246:
                    return WITH;
                case 245:
                    return TO;
                case 244:
                    return REQUIRES;
                case 243:
                    return YIELD;
                case 242:
                    return WHILE;
                case 241:
                    return VOLATILE;
                case 240:
                    return VOID;
                case 239:
                    return TRY;
                case 238:
                    return TRUE;
                case 237:
                    return TRANSIENT;
                case 236:
                    return THROWS;
                case 235:
                    return THROW;
                case 234:
                    return THIS;
                case 233:
                    return SYNCHRONIZED;
                case 232:
                    return SWITCH;
                case 231:
                    return SUPER;
                case 230:
                    return STRICTFP;
                case 229:
                    return STATIC;
                case 228:
                    return SHORT;
                case 227:
                    return RETURN;
                case 226:
                    return RECORD;
                case 225:
                    return PUBLIC;
                case 224:
                    return PROTECTED;
                case 223:
                    return PRIVATE;
                case 222:
                    return PACKAGE;
                case 221:
                    return NULL;
                case 220:
                    return NEW;
                case 219:
                    return NATIVE;
                case 218:
                    return LONG;
                case 217:
                    return INTERFACE;
                case 216:
                    return INT;
                case 215:
                    return INSTANCEOF;
                case 214:
                    return IMPORT;
                case 213:
                    return IMPLEMENTS;
                case 212:
                    return IF;
                case 211:
                    return GOTO;
                case 210:
                    return FOR;
                case 209:
                    return FLOAT;
                case 208:
                    return FINALLY;
                case 207:
                    return FINAL;
                case 206:
                    return FALSE;
                case 205:
                    return EXTENDS;
                case 204:
                    return ENUM;
                case 203:
                    return ELSE;
                case 202:
                    return DOUBLE;
                case 201:
                    return DO;
                case 200:
                    return _DEFAULT;
                case 199:
                    return CONTINUE;
                case 198:
                    return CONST;
                case 197:
                    return CLASS;
                case 196:
                    return CHAR;
                case 195:
                    return CATCH;
                case 194:
                    return CASE;
                case 193:
                    return BYTE;
                case 192:
                    return BREAK;
                case 191:
                    return BOOLEAN;
                case 190:
                    return ASSERT;
                case 189:
                    return ABSTRACT;
                case 188:
                    return COMMENT_CONTENT;
                case 187:
                    return MULTI_LINE_COMMENT;
                case 186:
                    return JAVADOC_COMMENT;
                case 185:
                    return JML_BLOCK_COMMENT;
                case 184:
                    return ENTER_MULTILINE_COMMENT;
                case 183:
                    return ENTER_JML_BLOCK_COMMENT;
                case 182:
                    return ENTER_JAVADOC_COMMENT;
                case 181:
                    return SINGLE_LINE_COMMENT;
                case 180:
                    return JML_LINE_COMMENT;
                case 179:
                    return DOTDOT;
                case 178:
                    return WRITABLE;
                case 177:
                    return WORKING_SPACE_REDUNDANTLY;
                case 176:
                    return WORKING_SPACE;
                case 175:
                    return WORKING_SPACE_ESC;
                case 174:
                    return WHEN_REDUNDANTLY;
                case 173:
                    return WHEN;
                case 172:
                    return WARN_OP;
                case 171:
                    return WARN;
                case 170:
                    return UNREACHABLE;
                case 169:
                    return UNKNOWN_OP_EQ;
                case 168:
                    return UNKNOWN_OP;
                case 167:
                    return UNINITIALIZED;
                case 166:
                    return TYPE;
                case 165:
                    return SUM;
                case 164:
                    return SUCH_THAT;
                case 163:
                    return SUBTYPE;
                case 162:
                    return STRICTLY_PURE;
                case 161:
                    return STATIC_INITIALIZER;
                case 160:
                    return SPEC_SAFE_MATH;
                case 159:
                    return SPEC_PUBLIC;
                case 158:
                    return SPEC_PROTECTED;
                case 157:
                    return SPEC_PRIVATE;
                case 156:
                    return SPEC_PACKAGE;
                case 155:
                    return SPEC_JAVA_MATH;
                case 154:
                    return SPEC_BIGINT_MATH;
                case 153:
                    return SIGNALS_REDUNDANTLY;
                case 152:
                    return SIGNALS_ONLY_REDUNDANTLY;
                case 151:
                    return SIGNALS_ONLY;
                case 150:
                    return SIGNALS;
                case 149:
                    return SET;
                case 148:
                    return SAFE_MATH;
                case 147:
                    return RETURN_BEHAVIOUR;
                case 146:
                    return RETURN_BEHAVIOR;
                case 145:
                    return RETURNS_REDUNDANTLY;
                case 144:
                    return RETURNS;
                case 143:
                    return RESULT;
                case 142:
                    return REQUIRES_REDUNDANTLY;
                case 141:
                    return REPRESENTS_REDUNDANTLY;
                case 140:
                    return REPRESENTS;
                case 139:
                    return REFINING;
                case 138:
                    return READABLE;
                case 137:
                    return PURE;
                case 136:
                    return PRODUCT;
                case 135:
                    return PRE_REDUNDANTLY;
                case 134:
                    return PRE;
                case 133:
                    return PRE_ESC;
                case 132:
                    return POST_REDUNDANTLY;
                case 131:
                    return POST;
                case 130:
                    return OR;
                case 129:
                    return OLD;
                case 128:
                    return NUM_OF;
                case 127:
                    return NULLABLE_BY_DEFAULT;
                case 126:
                    return NULLABLE;
                case 125:
                    return NOWARN_OP;
                case 124:
                    return NOWARN;
                case 123:
                    return NORMAL_EXAMPLE;
                case 122:
                    return NORMAL_BEHAVIOUR;
                case 121:
                    return NORMAL_BEHAVIOR;
                case 120:
                    return NON_NULL;
                case 119:
                    return NONNULLELEMENTS;
                case 118:
                    return NEW_OBJECT;
                case 117:
                    return NESTED_CONTRACT_START;
                case 116:
                    return NESTED_CONTRACT_END;
                case 115:
                    return MONITORS_FOR;
                case 114:
                    return MONITORED;
                case 113:
                    return MODIFIES_REDUNDANTLY;
                case 112:
                    return MODIFIES;
                case 111:
                    return LOOP_MODIFIES;
                case 110:
                    return MODIFIABLE_REDUNDANTLY;
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
                    return ESC_MEASURED_BY;
                case 102:
                    return MEASURED_BY;
                case 101:
                    return MAX;
                case 100:
                    return MAPS_REDUNDANTLY;
                case 99:
                    return MAPS;
                case 98:
                    return MAINTAINING_REDUNDANTLY;
                case 97:
                    return MAINTAINING;
                case 96:
                    return LOOP_INVARIANT_REDUNDANTLY;
                case 95:
                    return LOOP_INVARIANT_FREE;
                case 94:
                    return LOOP_INVARIANT;
                case 93:
                    return LOOP_CONTRACT;
                case 92:
                    return JAVA_MATH;
                case 91:
                    return IN_REDUNDANTLY;
                case 90:
                    return INVARIANT_REDUNDANTLY;
                case 89:
                    return NON_NULL_BY_DEFAULT;
                case 88:
                    return NO_STATE;
                case 87:
                    return TWO_STATE;
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
                    return HENCE_BY_REDUNDANTLY;
                case 80:
                    return HENCE_BY;
                case 79:
                    return HELPER;
                case 78:
                    return GHOST;
                case 77:
                    return FOR_EXAMPLE;
                case 76:
                    return FORALL;
                case 75:
                    return FORALLQ;
                case 74:
                    return FIELD;
                case 73:
                    return EXTRACT;
                case 72:
                    return EXSURES_REDUNDANTLY;
                case 71:
                    return EXSURES;
                case 70:
                    return EXISTS;
                case 69:
                    return EXCEPTIONAL_EXAMPLE;
                case 68:
                    return EXCEPTIONAL_BEHAVIOUR;
                case 67:
                    return EXCEPTIONAL_BEHAVIOR;
                case 66:
                    return EXAMPLE;
                case 65:
                    return ERASES;
                case 64:
                    return IMPLICATION_BACKWARD;
                case 63:
                    return IMPLICATION;
                case 62:
                    return EQUIVALENCE;
                case 61:
                    return REQUIRES_FREE;
                case 60:
                    return ENSURES_FREE;
                case 59:
                    return ENSURES_REDUNDANTLY;
                case 58:
                    return ENSURES;
                case 57:
                    return ELEMTYPE;
                case 56:
                    return DURATION_REDUNDANTLY;
                case 55:
                    return DURATION;
                case 54:
                    return DIVERGES_REDUNDANTLY;
                case 53:
                    return DIVERGES;
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
                    return CODE_SAFE_MATH;
                case 38:
                    return CODE_JAVA_MATH;
                case 37:
                    return CODE_BIGINT_MATH;
                case 36:
                    return CODE;
                case 35:
                    return CHOOSE_IF;
                case 34:
                    return CHOOSE;
                case 33:
                    return CAPTURES_REDUNDANTLY;
                case 32:
                    return CAPTURES;
                case 31:
                    return CALLABLE_REDUNDANTLY;
                case 30:
                    return CALLABLE;
                case 29:
                    return BREAK_BEHAVIOUR;
                case 28:
                    return BREAK_BEHAVIOR;
                case 27:
                    return BREAKS_REDUNDANTLY;
                case 26:
                    return BREAKS;
                case 25:
                    return BIGINT_MATH;
                case 24:
                    return BIGINT;
                case 23:
                    return BEHAVIOUR;
                case 22:
                    return BEHAVIOR;
                case 21:
                    return AXIOM;
                case 20:
                    return ASSUME_REDUNDANTLY;
                case 19:
                    return ASSUME;
                case 18:
                    return ASSIGNABLE_REDUNDANTLY;
                case 17:
                    return ASSIGNABLE;
                case 16:
                    return ASSERT_REDUNDANTLY;
                case 15:
                    return ANTIVALENCE;
                case 14:
                    return ALSO;
                case 13:
                    return ACCESSIBLE_REDUNDANTLY;
                case 12:
                    return ACCESSIBLE;
                case 11:
                    return MODEL_BEHAVIOUR;
                case 10:
                    return MODEL_BEHAVIOR;
                case 9:
                    return ABRUPT_BEHAVIOUR;
                case 8:
                    return ABRUPT_BEHAVIOR;
                case 7:
                    return INVARIANT;
                case 6:
                    return OLD_MAC_EOL;
                case 5:
                    return UNIX_EOL;
                case 4:
                    return WINDOWS_EOL;
                case 3:
                    return SPACE;
                case 2:
                    return JML_IGNORE_SINGLE_LINE_START;
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
