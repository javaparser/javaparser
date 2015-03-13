/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2015 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with JavaParser.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.github.javaparser.parser;

import com.github.javaparser.ast.lexical.*;

/**
 * @author Didier Villevalois
 */
class TokenLexemeConversion {

    static Lexeme instantiate(int kind, final String image) {
        switch (kind) {
            case ASTParserConstants.EOF:
                return new Whitespace(WhitespaceKind.END_OF_FILE, image);
            case ASTParserConstants.WHITESPACE:
                return new Whitespace(WhitespaceKind.NORMAL, image);
            case ASTParserConstants.NEWLINE:
                return new Whitespace(WhitespaceKind.LINE_ENDING, image);
            case ASTParserConstants.SINGLE_LINE_COMMENT:
                return new Comment(CommentKind.SINGLE_LINE, image);
            case ASTParserConstants.JAVA_DOC_COMMENT:
                return new Comment(CommentKind.JAVA_DOC, image);
            case ASTParserConstants.MULTI_LINE_COMMENT:
                return new Comment(CommentKind.MULTI_LINE, image);
            case ASTParserConstants.ABSTRACT:
                return new Keyword(KeywordKind.ABSTRACT);
            case ASTParserConstants.ASSERT:
                return new Keyword(KeywordKind.ASSERT);
            case ASTParserConstants.BOOLEAN:
                return new Keyword(KeywordKind.BOOLEAN);
            case ASTParserConstants.BREAK:
                return new Keyword(KeywordKind.BREAK);
            case ASTParserConstants.BYTE:
                return new Keyword(KeywordKind.BYTE);
            case ASTParserConstants.CASE:
                return new Keyword(KeywordKind.CASE);
            case ASTParserConstants.CATCH:
                return new Keyword(KeywordKind.CATCH);
            case ASTParserConstants.CHAR:
                return new Keyword(KeywordKind.CHAR);
            case ASTParserConstants.CLASS:
                return new Keyword(KeywordKind.CLASS);
            case ASTParserConstants.CONST:
                return new Keyword(KeywordKind.CONST);
            case ASTParserConstants.CONTINUE:
                return new Keyword(KeywordKind.CONTINUE);
            case ASTParserConstants._DEFAULT:
                return new Keyword(KeywordKind.DEFAULT);
            case ASTParserConstants.DO:
                return new Keyword(KeywordKind.DO);
            case ASTParserConstants.DOUBLE:
                return new Keyword(KeywordKind.DOUBLE);
            case ASTParserConstants.ELSE:
                return new Keyword(KeywordKind.ELSE);
            case ASTParserConstants.ENUM:
                return new Keyword(KeywordKind.ENUM);
            case ASTParserConstants.EXTENDS:
                return new Keyword(KeywordKind.EXTENDS);
            case ASTParserConstants.FALSE:
                return new Keyword(KeywordKind.FALSE);
            case ASTParserConstants.FINAL:
                return new Keyword(KeywordKind.FINAL);
            case ASTParserConstants.FINALLY:
                return new Keyword(KeywordKind.FINALLY);
            case ASTParserConstants.FLOAT:
                return new Keyword(KeywordKind.FLOAT);
            case ASTParserConstants.FOR:
                return new Keyword(KeywordKind.FOR);
            case ASTParserConstants.GOTO:
                return new Keyword(KeywordKind.GOTO);
            case ASTParserConstants.IF:
                return new Keyword(KeywordKind.IF);
            case ASTParserConstants.IMPLEMENTS:
                return new Keyword(KeywordKind.IMPLEMENTS);
            case ASTParserConstants.IMPORT:
                return new Keyword(KeywordKind.IMPORT);
            case ASTParserConstants.INSTANCEOF:
                return new Keyword(KeywordKind.INSTANCEOF);
            case ASTParserConstants.INT:
                return new Keyword(KeywordKind.INT);
            case ASTParserConstants.INTERFACE:
                return new Keyword(KeywordKind.INTERFACE);
            case ASTParserConstants.LONG:
                return new Keyword(KeywordKind.LONG);
            case ASTParserConstants.NATIVE:
                return new Keyword(KeywordKind.NATIVE);
            case ASTParserConstants.NEW:
                return new Keyword(KeywordKind.NEW);
            case ASTParserConstants.NULL:
                return new Keyword(KeywordKind.NULL);
            case ASTParserConstants.PACKAGE:
                return new Keyword(KeywordKind.PACKAGE);
            case ASTParserConstants.PRIVATE:
                return new Keyword(KeywordKind.PRIVATE);
            case ASTParserConstants.PROTECTED:
                return new Keyword(KeywordKind.PROTECTED);
            case ASTParserConstants.PUBLIC:
                return new Keyword(KeywordKind.PUBLIC);
            case ASTParserConstants.RETURN:
                return new Keyword(KeywordKind.RETURN);
            case ASTParserConstants.SHORT:
                return new Keyword(KeywordKind.SHORT);
            case ASTParserConstants.STATIC:
                return new Keyword(KeywordKind.STATIC);
            case ASTParserConstants.STRICTFP:
                return new Keyword(KeywordKind.STRICTFP);
            case ASTParserConstants.SUPER:
                return new Keyword(KeywordKind.SUPER);
            case ASTParserConstants.SWITCH:
                return new Keyword(KeywordKind.SWITCH);
            case ASTParserConstants.SYNCHRONIZED:
                return new Keyword(KeywordKind.SYNCHRONIZED);
            case ASTParserConstants.THIS:
                return new Keyword(KeywordKind.THIS);
            case ASTParserConstants.THROW:
                return new Keyword(KeywordKind.THROW);
            case ASTParserConstants.THROWS:
                return new Keyword(KeywordKind.THROWS);
            case ASTParserConstants.TRANSIENT:
                return new Keyword(KeywordKind.TRANSIENT);
            case ASTParserConstants.TRUE:
                return new Keyword(KeywordKind.TRUE);
            case ASTParserConstants.TRY:
                return new Keyword(KeywordKind.TRY);
            case ASTParserConstants.VOID:
                return new Keyword(KeywordKind.VOID);
            case ASTParserConstants.VOLATILE:
                return new Keyword(KeywordKind.VOLATILE);
            case ASTParserConstants.WHILE:
                return new Keyword(KeywordKind.WHILE);
            case ASTParserConstants.LONG_LITERAL:
                return new Literal(LiteralKind.LONG, image);
            case ASTParserConstants.INTEGER_LITERAL:
                return new Literal(LiteralKind.INTEGER, image);
            case ASTParserConstants.DECIMAL_LITERAL:
                return new Literal(LiteralKind.DECIMAL, image);
            case ASTParserConstants.HEX_LITERAL:
                return new Literal(LiteralKind.HEX, image);
            case ASTParserConstants.OCTAL_LITERAL:
                return new Literal(LiteralKind.OCTAL, image);
            case ASTParserConstants.BINARY_LITERAL:
                return new Literal(LiteralKind.BINARY, image);
            case ASTParserConstants.FLOATING_POINT_LITERAL:
                return new Literal(LiteralKind.FLOATING_POINT, image);
            case ASTParserConstants.DECIMAL_FLOATING_POINT_LITERAL:
                return new Literal(LiteralKind.DECIMAL_FLOATING_POINT, image);
            case ASTParserConstants.DECIMAL_EXPONENT:
                return new Literal(LiteralKind.DECIMAL_EXPONENT, image);
            case ASTParserConstants.HEXADECIMAL_FLOATING_POINT_LITERAL:
                return new Literal(LiteralKind.HEXADECIMAL_FLOATING_POINT, image);
            case ASTParserConstants.HEXADECIMAL_EXPONENT:
                return new Literal(LiteralKind.HEXADECIMAL_EXPONENT, image);
            case ASTParserConstants.CHARACTER_LITERAL:
                return new Literal(LiteralKind.CHARACTER, image);
            case ASTParserConstants.STRING_LITERAL:
                return new Literal(LiteralKind.STRING, image);
            case ASTParserConstants.IDENTIFIER:
                return new Identifier(image);
            case ASTParserConstants.LETTER:
                return new Identifier(image);
            case ASTParserConstants.PART_LETTER:
                return new Identifier(image);
            case ASTParserConstants.LPAREN:
                return new Separator(SeparatorKind.LPAREN);
            case ASTParserConstants.RPAREN:
                return new Separator(SeparatorKind.RPAREN);
            case ASTParserConstants.LBRACE:
                return new Separator(SeparatorKind.LBRACE);
            case ASTParserConstants.RBRACE:
                return new Separator(SeparatorKind.RBRACE);
            case ASTParserConstants.LBRACKET:
                return new Separator(SeparatorKind.LBRACKET);
            case ASTParserConstants.RBRACKET:
                return new Separator(SeparatorKind.RBRACKET);
            case ASTParserConstants.SEMICOLON:
                return new Separator(SeparatorKind.SEMICOLON);
            case ASTParserConstants.COMMA:
                return new Separator(SeparatorKind.COMMA);
            case ASTParserConstants.DOT:
                return new Separator(SeparatorKind.DOT);
            case ASTParserConstants.AT:
                return new Separator(SeparatorKind.AT);
            case ASTParserConstants.ASSIGN:
                return new Operator(OperatorKind.ASSIGN);
            case ASTParserConstants.LT:
                return new Operator(OperatorKind.LT);
            case ASTParserConstants.BANG:
                return new Operator(OperatorKind.BANG);
            case ASTParserConstants.TILDE:
                return new Operator(OperatorKind.TILDE);
            case ASTParserConstants.HOOK:
                return new Operator(OperatorKind.HOOK);
            case ASTParserConstants.COLON:
                return new Operator(OperatorKind.COLON);
            case ASTParserConstants.EQ:
                return new Operator(OperatorKind.EQ);
            case ASTParserConstants.LE:
                return new Operator(OperatorKind.LE);
            case ASTParserConstants.GE:
                return new Operator(OperatorKind.GE);
            case ASTParserConstants.NE:
                return new Operator(OperatorKind.NE);
            case ASTParserConstants.SC_OR:
                return new Operator(OperatorKind.SC_OR);
            case ASTParserConstants.SC_AND:
                return new Operator(OperatorKind.SC_AND);
            case ASTParserConstants.INCR:
                return new Operator(OperatorKind.INCR);
            case ASTParserConstants.DECR:
                return new Operator(OperatorKind.DECR);
            case ASTParserConstants.PLUS:
                return new Operator(OperatorKind.PLUS);
            case ASTParserConstants.MINUS:
                return new Operator(OperatorKind.MINUS);
            case ASTParserConstants.STAR:
                return new Operator(OperatorKind.STAR);
            case ASTParserConstants.SLASH:
                return new Operator(OperatorKind.SLASH);
            case ASTParserConstants.BIT_AND:
                return new Operator(OperatorKind.BIT_AND);
            case ASTParserConstants.BIT_OR:
                return new Operator(OperatorKind.BIT_OR);
            case ASTParserConstants.XOR:
                return new Operator(OperatorKind.XOR);
            case ASTParserConstants.REM:
                return new Operator(OperatorKind.REM);
            case ASTParserConstants.LSHIFT:
                return new Operator(OperatorKind.LSHIFT);
            case ASTParserConstants.DIAMOND:
                return new Operator(OperatorKind.DIAMOND);
            case ASTParserConstants.PLUSASSIGN:
                return new Operator(OperatorKind.PLUSASSIGN);
            case ASTParserConstants.MINUSASSIGN:
                return new Operator(OperatorKind.MINUSASSIGN);
            case ASTParserConstants.STARASSIGN:
                return new Operator(OperatorKind.STARASSIGN);
            case ASTParserConstants.SLASHASSIGN:
                return new Operator(OperatorKind.SLASHASSIGN);
            case ASTParserConstants.ANDASSIGN:
                return new Operator(OperatorKind.ANDASSIGN);
            case ASTParserConstants.ORASSIGN:
                return new Operator(OperatorKind.ORASSIGN);
            case ASTParserConstants.XORASSIGN:
                return new Operator(OperatorKind.XORASSIGN);
            case ASTParserConstants.REMASSIGN:
                return new Operator(OperatorKind.REMASSIGN);
            case ASTParserConstants.LSHIFTASSIGN:
                return new Operator(OperatorKind.LSHIFTASSIGN);
            case ASTParserConstants.RSIGNEDSHIFTASSIGN:
                return new Operator(OperatorKind.RSIGNEDSHIFTASSIGN);
            case ASTParserConstants.RUNSIGNEDSHIFTASSIGN:
                return new Operator(OperatorKind.RUNSIGNEDSHIFTASSIGN);
            case ASTParserConstants.ELLIPSIS:
                return new Operator(OperatorKind.ELLIPSIS);
            case ASTParserConstants.ARROW:
                return new Operator(OperatorKind.ARROW);
            case ASTParserConstants.DOUBLECOLON:
                return new Operator(OperatorKind.DOUBLECOLON);
            case ASTParserConstants.RUNSIGNEDSHIFT:
                return new Operator(OperatorKind.RUNSIGNEDSHIFT);
            case ASTParserConstants.RSIGNEDSHIFT:
                return new Operator(OperatorKind.RSIGNEDSHIFT);
            case ASTParserConstants.GT:
                return new Operator(OperatorKind.GT);

            default:
                throw new IllegalArgumentException();
        }
    }
}
