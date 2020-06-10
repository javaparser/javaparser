package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.EnumDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.SwitchStmt;
import org.junit.jupiter.api.Test;

import java.util.List;

import static com.github.javaparser.ParserConfiguration.LanguageLevel.RAW;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class LexicalPreservationWithTokenKindGeneratorTest {


    @Test
    public void foo() {
        String originalCode = "" +
                "/*\n" +
                " * Copyright (C) 2007-2010 Júlio Vilmar Gesser.\n" +
                " * Copyright (C) 2011, 2013-2020 The JavaParser Team.\n" +
                " *\n" +
                " * This file is part of JavaParser.\n" +
                " *\n" +
                " * JavaParser can be used either under the terms of\n" +
                " * a) the GNU Lesser General Public License as published by\n" +
                " *     the Free Software Foundation, either version 3 of the License, or\n" +
                " *     (at your option) any later version.\n" +
                " * b) the terms of the Apache License\n" +
                " *\n" +
                " * You should have received a copy of both licenses in LICENCE.LGPL and\n" +
                " * LICENCE.APACHE. Please refer to those files for details.\n" +
                " *\n" +
                " * JavaParser is distributed in the hope that it will be useful,\n" +
                " * but WITHOUT ANY WARRANTY; without even the implied warranty of\n" +
                " * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n" +
                " * GNU Lesser General Public License for more details.\n" +
                " */\n" +
                "package com.github.javaparser;\n" +
                "\n" +
                "import java.util.List;\n" +
                "import java.util.Optional;\n" +
                "import static com.github.javaparser.utils.CodeGenerationUtils.f;\n" +
                "import static com.github.javaparser.utils.Utils.SYSTEM_EOL;\n" +
                "import static com.github.javaparser.utils.Utils.assertNotNull;\n" +
                "import com.github.javaparser.ast.Generated;\n" +
                "\n" +
                "/**\n" +
                " * A token from a parsed source file.\n" +
                " * (Awkwardly named \"Java\"Token since JavaCC already generates an internal class Token.)\n" +
                " * It is a node in a double linked list called token list.\n" +
                " */\n" +
                "public class JavaToken {\n" +
                "\n" +
                "    public static final JavaToken INVALID = new JavaToken();\n" +
                "\n" +
                "    private Range range;\n" +
                "\n" +
                "    private int kind;\n" +
                "\n" +
                "    private String text;\n" +
                "\n" +
                "    private JavaToken previousToken = null;\n" +
                "\n" +
                "    private JavaToken nextToken = null;\n" +
                "\n" +
                "    private JavaToken() {\n" +
                "        this(null, 0, \"INVALID\", null, null);\n" +
                "    }\n" +
                "\n" +
                "    public JavaToken(int kind, String text) {\n" +
                "        this(null, kind, text, null, null);\n" +
                "    }\n" +
                "\n" +
                "    JavaToken(Token token, List<JavaToken> tokens) {\n" +
                "        // You could be puzzled by the following lines\n" +
                "        // \n" +
                "        // The reason why these lines are necessary is the fact that Java is ambiguous. There are cases where the\n" +
                "        // sequence of characters \">>>\" and \">>\" should be recognized as the single tokens \">>>\" and \">>\". In other\n" +
                "        // cases however we want to split those characters in single GT tokens (\">\").\n" +
                "        // \n" +
                "        // For example, in expressions \">>\" and \">>>\" are valid, while when defining types we could have this:\n" +
                "        // \n" +
                "        // List<List<Set<String>>>>\n" +
                "        // \n" +
                "        // You can see that the sequence \">>>>\" should be interpreted as four consecutive \">\" tokens closing a type\n" +
                "        // parameter list.\n" +
                "        // \n" +
                "        // The JavaCC handle this case by first recognizing always the longest token, and then depending on the context\n" +
                "        // putting back the unused chars in the stream. However in those cases the token provided is invalid: it has an\n" +
                "        // image corresponding to the text originally recognized, without considering that after some characters could\n" +
                "        // have been put back into the stream.\n" +
                "        // \n" +
                "        // So in the case of:\n" +
                "        // \n" +
                "        // List<List<Set<String>>>>\n" +
                "        // ___   -> recognized as \">>>\", then \">>\" put back in the stream but Token(type=GT, image=\">>>\") passed to this class\n" +
                "        // ___  -> recognized as \">>>\", then \">>\" put back in the stream but Token(type=GT, image=\">>>\") passed to this class\n" +
                "        // __  -> recognized as \">>\", then \">\" put back in the stream but Token(type=GT, image=\">>\") passed to this class\n" +
                "        // _  -> Token(type=GT, image=\">\") good!\n" +
                "        // \n" +
                "        // So given the image could be wrong but the type is correct, we look at the type of the token and we fix\n" +
                "        // the image. Everybody is happy and we can keep this horrible thing as our little secret.\n" +
                "        Range range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.endColumn);\n" +
                "        String text = token.image;\n" +
                "        if (token.kind == GeneratedJavaParserConstants.GT) {\n" +
                "            range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.beginColumn);\n" +
                "            text = \">\";\n" +
                "        } else if (token.kind == GeneratedJavaParserConstants.RSIGNEDSHIFT) {\n" +
                "            range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.beginColumn + 1);\n" +
                "            text = \">>\";\n" +
                "        }\n" +
                "        this.range = range;\n" +
                "        this.kind = token.kind;\n" +
                "        this.text = text;\n" +
                "        if (!tokens.isEmpty()) {\n" +
                "            final JavaToken previousToken = tokens.get(tokens.size() - 1);\n" +
                "            this.previousToken = previousToken;\n" +
                "            previousToken.nextToken = this;\n" +
                "        } else {\n" +
                "            previousToken = null;\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * Create a token of a certain kind.\n" +
                "     */\n" +
                "    public JavaToken(int kind) {\n" +
                "        String content = GeneratedJavaParserConstants.tokenImage[kind];\n" +
                "        if (content.startsWith(\"\\\"\")) {\n" +
                "            content = content.substring(1, content.length() - 1);\n" +
                "        }\n" +
                "        if (TokenTypes.isEndOfLineToken(kind)) {\n" +
                "            content = SYSTEM_EOL;\n" +
                "        } else if (TokenTypes.isWhitespace(kind)) {\n" +
                "            content = \" \";\n" +
                "        }\n" +
                "        this.kind = kind;\n" +
                "        this.text = content;\n" +
                "    }\n" +
                "\n" +
                "    public JavaToken(Range range, int kind, String text, JavaToken previousToken, JavaToken nextToken) {\n" +
                "        assertNotNull(text);\n" +
                "        this.range = range;\n" +
                "        this.kind = kind;\n" +
                "        this.text = text;\n" +
                "        this.previousToken = previousToken;\n" +
                "        this.nextToken = nextToken;\n" +
                "    }\n" +
                "\n" +
                "    public Optional<Range> getRange() {\n" +
                "        return Optional.ofNullable(range);\n" +
                "    }\n" +
                "\n" +
                "    public int getKind() {\n" +
                "        return kind;\n" +
                "    }\n" +
                "\n" +
                "    void setKind(int kind) {\n" +
                "        this.kind = kind;\n" +
                "    }\n" +
                "\n" +
                "    public String getText() {\n" +
                "        return text;\n" +
                "    }\n" +
                "\n" +
                "    public Optional<JavaToken> getNextToken() {\n" +
                "        return Optional.ofNullable(nextToken);\n" +
                "    }\n" +
                "\n" +
                "    public Optional<JavaToken> getPreviousToken() {\n" +
                "        return Optional.ofNullable(previousToken);\n" +
                "    }\n" +
                "\n" +
                "    public void setRange(Range range) {\n" +
                "        this.range = range;\n" +
                "    }\n" +
                "\n" +
                "    public void setText(String text) {\n" +
                "        this.text = text;\n" +
                "    }\n" +
                "\n" +
                "    public String asString() {\n" +
                "        return text;\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * @return the token range that goes from the beginning to the end of the token list this token is a part of.\n" +
                "     */\n" +
                "    public TokenRange toTokenRange() {\n" +
                "        return new TokenRange(findFirstToken(), findLastToken());\n" +
                "    }\n" +
                "\n" +
                "    @Override\n" +
                "    public String toString() {\n" +
                "        String text = getText().replace(\"\\n\", \"\\\\n\").replace(\"\\r\", \"\\\\r\").replace(\"\\r\\n\", \"\\\\r\\\\n\").replace(\"\\t\", \"\\\\t\");\n" +
                "        return f(\"\\\"%s\\\"   <%s>   %s\", text, getKind(), getRange().map(Range::toString).orElse(\"(?)-(?)\"));\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * Used by the parser while constructing nodes. No tokens should be invalid when the parser is done.\n" +
                "     */\n" +
                "    public boolean valid() {\n" +
                "        return !invalid();\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * Used by the parser while constructing nodes. No tokens should be invalid when the parser is done.\n" +
                "     */\n" +
                "    public boolean invalid() {\n" +
                "        return this == INVALID;\n" +
                "    }\n" +
                "\n" +
                "    public enum Category {\n" +
                "\n" +
                "        WHITESPACE_NO_EOL,\n" +
                "        EOL,\n" +
                "        COMMENT,\n" +
                "        IDENTIFIER,\n" +
                "        KEYWORD,\n" +
                "        LITERAL,\n" +
                "        SEPARATOR,\n" +
                "        OPERATOR;\n" +
                "\n" +
                "        public boolean isWhitespaceOrComment() {\n" +
                "            return isWhitespace() || this == COMMENT;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isWhitespace() {\n" +
                "            return this == WHITESPACE_NO_EOL || this == EOL;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isEndOfLine() {\n" +
                "            return this == EOL;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isComment() {\n" +
                "            return this == COMMENT;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isWhitespaceButNotEndOfLine() {\n" +
                "            return this == WHITESPACE_NO_EOL;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isIdentifier() {\n" +
                "            return this == IDENTIFIER;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isKeyword() {\n" +
                "            return this == KEYWORD;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isLiteral() {\n" +
                "            return this == LITERAL;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isSeparator() {\n" +
                "            return this == SEPARATOR;\n" +
                "        }\n" +
                "\n" +
                "        public boolean isOperator() {\n" +
                "            return this == OPERATOR;\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    @Generated(\"com.github.javaparser.generator.core.other.TokenKindGenerator\")\n" +
                "    public enum Kind {\n" +
                "\n" +
                "        EOF(0),\n" +
                "        SPACE(1),\n" +
                "        WINDOWS_EOL(2),\n" +
                "        UNIX_EOL(3),\n" +
                "        OLD_MAC_EOL(4),\n" +
                "        SINGLE_LINE_COMMENT(5),\n" +
                "        ENTER_JAVADOC_COMMENT(6),\n" +
                "        ENTER_MULTILINE_COMMENT(7),\n" +
                "        JAVADOC_COMMENT(8),\n" +
                "        MULTI_LINE_COMMENT(9),\n" +
                "        COMMENT_CONTENT(10),\n" +
                "        ABSTRACT(11),\n" +
                "        ASSERT(12),\n" +
                "        BOOLEAN(13),\n" +
                "        BREAK(14),\n" +
                "        BYTE(15),\n" +
                "        CASE(16),\n" +
                "        CATCH(17),\n" +
                "        CHAR(18),\n" +
                "        CLASS(19),\n" +
                "        CONST(20),\n" +
                "        CONTINUE(21),\n" +
                "        _DEFAULT(22),\n" +
                "        DO(23),\n" +
                "        DOUBLE(24),\n" +
                "        ELSE(25),\n" +
                "        ENUM(26),\n" +
                "        EXTENDS(27),\n" +
                "        FALSE(28),\n" +
                "        FINAL(29),\n" +
                "        FINALLY(30),\n" +
                "        FLOAT(31),\n" +
                "        FOR(32),\n" +
                "        GOTO(33),\n" +
                "        IF(34),\n" +
                "        IMPLEMENTS(35),\n" +
                "        IMPORT(36),\n" +
                "        INSTANCEOF(37),\n" +
                "        INT(38),\n" +
                "        INTERFACE(39),\n" +
                "        LONG(40),\n" +
                "        NATIVE(41),\n" +
                "        NEW(42),\n" +
                "        NULL(43),\n" +
                "        PACKAGE(44),\n" +
                "        PRIVATE(45),\n" +
                "        PROTECTED(46),\n" +
                "        PUBLIC(47),\n" +
                "        RETURN(48),\n" +
                "        SHORT(49),\n" +
                "        STATIC(50),\n" +
                "        STRICTFP(51),\n" +
                "        SUPER(52),\n" +
                "        SWITCH(53),\n" +
                "        SYNCHRONIZED(54),\n" +
                "        THIS(55),\n" +
                "        THROW(56),\n" +
                "        THROWS(57),\n" +
                "        TRANSIENT(58),\n" +
                "        TRUE(59),\n" +
                "        TRY(60),\n" +
                "        VOID(61),\n" +
                "        VOLATILE(62),\n" +
                "        WHILE(63),\n" +
                "        YIELD(64),\n" +
                "        REQUIRES(65),\n" +
                "        TO(66),\n" +
                "        WITH(67),\n" +
                "        OPEN(68),\n" +
                "        OPENS(69),\n" +
                "        USES(70),\n" +
                "        MODULE(71),\n" +
                "        EXPORTS(72),\n" +
                "        PROVIDES(73),\n" +
                "        TRANSITIVE(74),\n" +
                "        LONG_LITERAL(75),\n" +
                "        INTEGER_LITERAL(76),\n" +
                "        DECIMAL_LITERAL(77),\n" +
                "        HEX_LITERAL(78),\n" +
                "        OCTAL_LITERAL(79),\n" +
                "        BINARY_LITERAL(80),\n" +
                "        FLOATING_POINT_LITERAL(81),\n" +
                "        DECIMAL_FLOATING_POINT_LITERAL(82),\n" +
                "        DECIMAL_EXPONENT(83),\n" +
                "        HEXADECIMAL_FLOATING_POINT_LITERAL(84),\n" +
                "        HEXADECIMAL_EXPONENT(85),\n" +
                "        HEX_DIGITS(86),\n" +
                "        UNICODE_ESCAPE(87),\n" +
                "        CHARACTER_LITERAL(88),\n" +
                "        STRING_LITERAL(89),\n" +
                "        ENTER_TEXT_BLOCK(90),\n" +
                "        TEXT_BLOCK_LITERAL(91),\n" +
                "        TEXT_BLOCK_CONTENT(92),\n" +
                "        IDENTIFIER(93),\n" +
                "        LETTER(94),\n" +
                "        PART_LETTER(95),\n" +
                "        LPAREN(96),\n" +
                "        RPAREN(97),\n" +
                "        LBRACE(98),\n" +
                "        RBRACE(99),\n" +
                "        LBRACKET(100),\n" +
                "        RBRACKET(101),\n" +
                "        SEMICOLON(102),\n" +
                "        COMMA(103),\n" +
                "        DOT(104),\n" +
                "        AT(105),\n" +
                "        ASSIGN(106),\n" +
                "        LT(107),\n" +
                "        BANG(108),\n" +
                "        TILDE(109),\n" +
                "        HOOK(110),\n" +
                "        COLON(111),\n" +
                "        EQ(112),\n" +
                "        LE(113),\n" +
                "        GE(114),\n" +
                "        NE(115),\n" +
                "        SC_OR(116),\n" +
                "        SC_AND(117),\n" +
                "        INCR(118),\n" +
                "        DECR(119),\n" +
                "        PLUS(120),\n" +
                "        MINUS(121),\n" +
                "        STAR(122),\n" +
                "        SLASH(123),\n" +
                "        BIT_AND(124),\n" +
                "        BIT_OR(125),\n" +
                "        XOR(126),\n" +
                "        REM(127),\n" +
                "        LSHIFT(128),\n" +
                "        PLUSASSIGN(129),\n" +
                "        MINUSASSIGN(130),\n" +
                "        STARASSIGN(131),\n" +
                "        SLASHASSIGN(132),\n" +
                "        ANDASSIGN(133),\n" +
                "        ORASSIGN(134),\n" +
                "        XORASSIGN(135),\n" +
                "        REMASSIGN(136),\n" +
                "        LSHIFTASSIGN(137),\n" +
                "        RSIGNEDSHIFTASSIGN(138),\n" +
                "        RUNSIGNEDSHIFTASSIGN(139),\n" +
                "        ELLIPSIS(140),\n" +
                "        ARROW(141),\n" +
                "        DOUBLECOLON(142),\n" +
                "        RUNSIGNEDSHIFT(143),\n" +
                "        RSIGNEDSHIFT(144),\n" +
                "        GT(145),\n" +
                "        CTRL_Z(146);\n" +
                "\n" +
                "        private final int kind;\n" +
                "\n" +
                "        Kind(int kind) {\n" +
                "            this.kind = kind;\n" +
                "        }\n" +
                "\n" +
                "        public static Kind valueOf(int kind) {\n" +
                "            switch(kind) {\n" +
                "                case 146:\n" +
                "                    return CTRL_Z;\n" +
                "                case 145:\n" +
                "                    return GT;\n" +
                "                case 144:\n" +
                "                    return RSIGNEDSHIFT;\n" +
                "                case 143:\n" +
                "                    return RUNSIGNEDSHIFT;\n" +
                "                case 142:\n" +
                "                    return DOUBLECOLON;\n" +
                "                case 141:\n" +
                "                    return ARROW;\n" +
                "                case 140:\n" +
                "                    return ELLIPSIS;\n" +
                "                case 139:\n" +
                "                    return RUNSIGNEDSHIFTASSIGN;\n" +
                "                case 138:\n" +
                "                    return RSIGNEDSHIFTASSIGN;\n" +
                "                case 137:\n" +
                "                    return LSHIFTASSIGN;\n" +
                "                case 136:\n" +
                "                    return REMASSIGN;\n" +
                "                case 135:\n" +
                "                    return XORASSIGN;\n" +
                "                case 134:\n" +
                "                    return ORASSIGN;\n" +
                "                case 133:\n" +
                "                    return ANDASSIGN;\n" +
                "                case 132:\n" +
                "                    return SLASHASSIGN;\n" +
                "                case 131:\n" +
                "                    return STARASSIGN;\n" +
                "                case 130:\n" +
                "                    return MINUSASSIGN;\n" +
                "                case 129:\n" +
                "                    return PLUSASSIGN;\n" +
                "                case 128:\n" +
                "                    return LSHIFT;\n" +
                "                case 127:\n" +
                "                    return REM;\n" +
                "                case 126:\n" +
                "                    return XOR;\n" +
                "                case 125:\n" +
                "                    return BIT_OR;\n" +
                "                case 124:\n" +
                "                    return BIT_AND;\n" +
                "                case 123:\n" +
                "                    return SLASH;\n" +
                "                case 122:\n" +
                "                    return STAR;\n" +
                "                case 121:\n" +
                "                    return MINUS;\n" +
                "                case 120:\n" +
                "                    return PLUS;\n" +
                "                case 119:\n" +
                "                    return DECR;\n" +
                "                case 118:\n" +
                "                    return INCR;\n" +
                "                case 117:\n" +
                "                    return SC_AND;\n" +
                "                case 116:\n" +
                "                    return SC_OR;\n" +
                "                case 115:\n" +
                "                    return NE;\n" +
                "                case 114:\n" +
                "                    return GE;\n" +
                "                case 113:\n" +
                "                    return LE;\n" +
                "                case 112:\n" +
                "                    return EQ;\n" +
                "                case 111:\n" +
                "                    return COLON;\n" +
                "                case 110:\n" +
                "                    return HOOK;\n" +
                "                case 109:\n" +
                "                    return TILDE;\n" +
                "                case 108:\n" +
                "                    return BANG;\n" +
                "                case 107:\n" +
                "                    return LT;\n" +
                "                case 106:\n" +
                "                    return ASSIGN;\n" +
                "                case 105:\n" +
                "                    return AT;\n" +
                "                case 104:\n" +
                "                    return DOT;\n" +
                "                case 103:\n" +
                "                    return COMMA;\n" +
                "                case 102:\n" +
                "                    return SEMICOLON;\n" +
                "                case 101:\n" +
                "                    return RBRACKET;\n" +
                "                case 100:\n" +
                "                    return LBRACKET;\n" +
                "                case 99:\n" +
                "                    return RBRACE;\n" +
                "                case 98:\n" +
                "                    return LBRACE;\n" +
                "                case 97:\n" +
                "                    return RPAREN;\n" +
                "                case 96:\n" +
                "                    return LPAREN;\n" +
                "                case 95:\n" +
                "                    return PART_LETTER;\n" +
                "                case 94:\n" +
                "                    return LETTER;\n" +
                "                case 93:\n" +
                "                    return IDENTIFIER;\n" +
                "                case 92:\n" +
                "                    return TEXT_BLOCK_CONTENT;\n" +
                "                case 91:\n" +
                "                    return TEXT_BLOCK_LITERAL;\n" +
                "                case 90:\n" +
                "                    return ENTER_TEXT_BLOCK;\n" +
                "                case 89:\n" +
                "                    return STRING_LITERAL;\n" +
                "                case 88:\n" +
                "                    return CHARACTER_LITERAL;\n" +
                "                case 87:\n" +
                "                    return UNICODE_ESCAPE;\n" +
                "                case 86:\n" +
                "                    return HEX_DIGITS;\n" +
                "                case 85:\n" +
                "                    return HEXADECIMAL_EXPONENT;\n" +
                "                case 84:\n" +
                "                    return HEXADECIMAL_FLOATING_POINT_LITERAL;\n" +
                "                case 83:\n" +
                "                    return DECIMAL_EXPONENT;\n" +
                "                case 82:\n" +
                "                    return DECIMAL_FLOATING_POINT_LITERAL;\n" +
                "                case 81:\n" +
                "                    return FLOATING_POINT_LITERAL;\n" +
                "                case 80:\n" +
                "                    return BINARY_LITERAL;\n" +
                "                case 79:\n" +
                "                    return OCTAL_LITERAL;\n" +
                "                case 78:\n" +
                "                    return HEX_LITERAL;\n" +
                "                case 77:\n" +
                "                    return DECIMAL_LITERAL;\n" +
                "                case 76:\n" +
                "                    return INTEGER_LITERAL;\n" +
                "                case 75:\n" +
                "                    return LONG_LITERAL;\n" +
                "                case 74:\n" +
                "                    return TRANSITIVE;\n" +
                "                case 73:\n" +
                "                    return PROVIDES;\n" +
                "                case 72:\n" +
                "                    return EXPORTS;\n" +
                "                case 71:\n" +
                "                    return MODULE;\n" +
                "                case 70:\n" +
                "                    return USES;\n" +
                "                case 69:\n" +
                "                    return OPENS;\n" +
                "                case 68:\n" +
                "                    return OPEN;\n" +
                "                case 67:\n" +
                "                    return WITH;\n" +
                "                case 66:\n" +
                "                    return TO;\n" +
                "                case 65:\n" +
                "                    return REQUIRES;\n" +
                "                case 64:\n" +
                "                    return YIELD;\n" +
                "                case 63:\n" +
                "                    return WHILE;\n" +
                "                case 62:\n" +
                "                    return VOLATILE;\n" +
                "                case 61:\n" +
                "                    return VOID;\n" +
                "                case 60:\n" +
                "                    return TRY;\n" +
                "                case 59:\n" +
                "                    return TRUE;\n" +
                "                case 58:\n" +
                "                    return TRANSIENT;\n" +
                "                case 57:\n" +
                "                    return THROWS;\n" +
                "                case 56:\n" +
                "                    return THROW;\n" +
                "                case 55:\n" +
                "                    return THIS;\n" +
                "                case 54:\n" +
                "                    return SYNCHRONIZED;\n" +
                "                case 53:\n" +
                "                    return SWITCH;\n" +
                "                case 52:\n" +
                "                    return SUPER;\n" +
                "                case 51:\n" +
                "                    return STRICTFP;\n" +
                "                case 50:\n" +
                "                    return STATIC;\n" +
                "                case 49:\n" +
                "                    return SHORT;\n" +
                "                case 48:\n" +
                "                    return RETURN;\n" +
                "                case 47:\n" +
                "                    return PUBLIC;\n" +
                "                case 46:\n" +
                "                    return PROTECTED;\n" +
                "                case 45:\n" +
                "                    return PRIVATE;\n" +
                "                case 44:\n" +
                "                    return PACKAGE;\n" +
                "                case 43:\n" +
                "                    return NULL;\n" +
                "                case 42:\n" +
                "                    return NEW;\n" +
                "                case 41:\n" +
                "                    return NATIVE;\n" +
                "                case 40:\n" +
                "                    return LONG;\n" +
                "                case 39:\n" +
                "                    return INTERFACE;\n" +
                "                case 38:\n" +
                "                    return INT;\n" +
                "                case 37:\n" +
                "                    return INSTANCEOF;\n" +
                "                case 36:\n" +
                "                    return IMPORT;\n" +
                "                case 35:\n" +
                "                    return IMPLEMENTS;\n" +
                "                case 34:\n" +
                "                    return IF;\n" +
                "                case 33:\n" +
                "                    return GOTO;\n" +
                "                case 32:\n" +
                "                    return FOR;\n" +
                "                case 31:\n" +
                "                    return FLOAT;\n" +
                "                case 30:\n" +
                "                    return FINALLY;\n" +
                "                case 29:\n" +
                "                    return FINAL;\n" +
                "                case 28:\n" +
                "                    return FALSE;\n" +
                "                case 27:\n" +
                "                    return EXTENDS;\n" +
                "                case 26:\n" +
                "                    return ENUM;\n" +
                "                case 25:\n" +
                "                    return ELSE;\n" +
                "                case 24:\n" +
                "                    return DOUBLE;\n" +
                "                case 23:\n" +
                "                    return DO;\n" +
                "                case 22:\n" +
                "                    return _DEFAULT;\n" +
                "                case 21:\n" +
                "                    return CONTINUE;\n" +
                "                case 20:\n" +
                "                    return CONST;\n" +
                "                case 19:\n" +
                "                    return CLASS;\n" +
                "                case 18:\n" +
                "                    return CHAR;\n" +
                "                case 17:\n" +
                "                    return CATCH;\n" +
                "                case 16:\n" +
                "                    return CASE;\n" +
                "                case 15:\n" +
                "                    return BYTE;\n" +
                "                case 14:\n" +
                "                    return BREAK;\n" +
                "                case 13:\n" +
                "                    return BOOLEAN;\n" +
                "                case 12:\n" +
                "                    return ASSERT;\n" +
                "                case 11:\n" +
                "                    return ABSTRACT;\n" +
                "                case 10:\n" +
                "                    return COMMENT_CONTENT;\n" +
                "                case 9:\n" +
                "                    return MULTI_LINE_COMMENT;\n" +
                "                case 8:\n" +
                "                    return JAVADOC_COMMENT;\n" +
                "                case 7:\n" +
                "                    return ENTER_MULTILINE_COMMENT;\n" +
                "                case 6:\n" +
                "                    return ENTER_JAVADOC_COMMENT;\n" +
                "                case 5:\n" +
                "                    return SINGLE_LINE_COMMENT;\n" +
                "                case 4:\n" +
                "                    return OLD_MAC_EOL;\n" +
                "                case 3:\n" +
                "                    return UNIX_EOL;\n" +
                "                case 2:\n" +
                "                    return WINDOWS_EOL;\n" +
                "                case 1:\n" +
                "                    return SPACE;\n" +
                "                case 0:\n" +
                "                    return EOF;\n" +
                "                default:\n" +
                "                    throw new IllegalArgumentException(f(\"Token kind %i is unknown.\", kind));\n" +
                "            }\n" +
                "        }\n" +
                "\n" +
                "        public boolean isPrimitive() {\n" +
                "            return this == BYTE || this == CHAR || this == SHORT || this == INT || this == LONG || this == FLOAT || this == DOUBLE;\n" +
                "        }\n" +
                "\n" +
                "        public int getKind() {\n" +
                "            return kind;\n" +
                "        }\n" +
                "    }\n" +
                "\n" +
                "    public JavaToken.Category getCategory() {\n" +
                "        return TokenTypes.getCategory(kind);\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * Inserts newToken into the token list just before this token.\n" +
                "     */\n" +
                "    public void insert(JavaToken newToken) {\n" +
                "        assertNotNull(newToken);\n" +
                "        getPreviousToken().ifPresent(p -> {\n" +
                "            p.nextToken = newToken;\n" +
                "            newToken.previousToken = p;\n" +
                "        });\n" +
                "        previousToken = newToken;\n" +
                "        newToken.nextToken = this;\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * Inserts newToken into the token list just after this token.\n" +
                "     */\n" +
                "    public void insertAfter(JavaToken newToken) {\n" +
                "        assertNotNull(newToken);\n" +
                "        getNextToken().ifPresent(n -> {\n" +
                "            n.previousToken = newToken;\n" +
                "            newToken.nextToken = n;\n" +
                "        });\n" +
                "        nextToken = newToken;\n" +
                "        newToken.previousToken = this;\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * Links the tokens around the current token together, making the current token disappear from the list.\n" +
                "     */\n" +
                "    public void deleteToken() {\n" +
                "        final Optional<JavaToken> nextToken = getNextToken();\n" +
                "        final Optional<JavaToken> previousToken = getPreviousToken();\n" +
                "        previousToken.ifPresent(p -> p.nextToken = nextToken.orElse(null));\n" +
                "        nextToken.ifPresent(n -> n.previousToken = previousToken.orElse(null));\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * Replaces the current token with newToken.\n" +
                "     */\n" +
                "    public void replaceToken(JavaToken newToken) {\n" +
                "        assertNotNull(newToken);\n" +
                "        getPreviousToken().ifPresent(p -> {\n" +
                "            p.nextToken = newToken;\n" +
                "            newToken.previousToken = p;\n" +
                "        });\n" +
                "        getNextToken().ifPresent(n -> {\n" +
                "            n.previousToken = newToken;\n" +
                "            newToken.nextToken = n;\n" +
                "        });\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * @return the last token in the token list.\n" +
                "     */\n" +
                "    public JavaToken findLastToken() {\n" +
                "        JavaToken current = this;\n" +
                "        while (current.getNextToken().isPresent()) {\n" +
                "            current = current.getNextToken().get();\n" +
                "        }\n" +
                "        return current;\n" +
                "    }\n" +
                "\n" +
                "    /**\n" +
                "     * @return the first token in the token list.\n" +
                "     */\n" +
                "    public JavaToken findFirstToken() {\n" +
                "        JavaToken current = this;\n" +
                "        while (current.getPreviousToken().isPresent()) {\n" +
                "            current = current.getPreviousToken().get();\n" +
                "        }\n" +
                "        return current;\n" +
                "    }\n" +
                "\n" +
                "    @Override\n" +
                "    public int hashCode() {\n" +
                "        int result = kind;\n" +
                "        result = 31 * result + text.hashCode();\n" +
                "        return result;\n" +
                "    }\n" +
                "\n" +
                "    @Override\n" +
                "    public boolean equals(Object o) {\n" +
                "        if (this == o)\n" +
                "            return true;\n" +
                "        if (o == null || getClass() != o.getClass())\n" +
                "            return false;\n" +
                "        JavaToken javaToken = (JavaToken) o;\n" +
                "        if (kind != javaToken.kind)\n" +
                "            return false;\n" +
                "        if (!text.equals(javaToken.text))\n" +
                "            return false;\n" +
                "        return true;\n" +
                "    }\n" +
                "}\n" +
                "";


        ParserConfiguration parserConfiguration = new ParserConfiguration()
                .setLanguageLevel(RAW)
//            .setStoreTokens(false)
//            .setAttributeComments(false)
                .setLexicalPreservationEnabled(true)
                ;

        JavaParser javaParser = new JavaParser(parserConfiguration);

        ParseResult<CompilationUnit> parseResult = javaParser.parse(originalCode);
        CompilationUnit javaTokenCu = parseResult.getResult().orElseThrow(RuntimeException::new);

        final ClassOrInterfaceDeclaration javaToken = javaTokenCu.getClassByName("JavaToken").orElseThrow(() -> new AssertionError("Can't find class in java file."));
        final EnumDeclaration kindEnum = javaToken.findFirst(EnumDeclaration.class, e -> e.getNameAsString().equals("Kind")).orElseThrow(() -> new AssertionError("Can't find class in java file."));

        List<MethodDeclaration> valueOfMethods = kindEnum.getMethodsByName("valueOf");
        if (valueOfMethods.size() != 1) {
            throw new AssertionError("Expected precisely one method named valueOf");
        }
        MethodDeclaration valueOfMethod = valueOfMethods.get(0);
        final SwitchStmt valueOfSwitch = valueOfMethod.findFirst(SwitchStmt.class).orElseThrow(() -> new AssertionError("Can't find valueOf switch."));


        // TODO: Define "reset"
        // Reset the enum:
        kindEnum.getEntries().clear();
        // Reset the switch within the method valueOf(), leaving only the default
//        valueOfSwitch.getEntries().stream().filter(e -> e.getLabels().isNonEmpty()).forEach(Node::remove);

        // TODO: Figure out why the newlines are not removed when we remove an entire switch entry...
        SwitchEntry defaultEntry = valueOfSwitch.getDefaultSwitchEntry().get();
        valueOfSwitch.getEntries().clear();
        valueOfSwitch.getEntries().add(defaultEntry);


        assertEquals(originalCode, LexicalPreservingPrinter.print(javaTokenCu));

    }
}
