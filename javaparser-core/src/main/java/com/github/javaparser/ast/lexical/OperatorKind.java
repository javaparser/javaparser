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

package com.github.javaparser.ast.lexical;

/**
* @author Didier Villevalois
*/
public enum OperatorKind {
    ASSIGN("="),
    LT("<"),
    BANG("!"),
    TILDE("~"),
    HOOK("?"),
    COLON(":"),
    EQ("=="),
    LE("<="),
    GE(">="),
    NE("!="),
    SC_OR("||"),
    SC_AND("&&"),
    INCR("++"),
    DECR("--"),
    PLUS("+"),
    MINUS("-"),
    STAR("*"),
    SLASH("/"),
    BIT_AND("&"),
    BIT_OR("|"),
    XOR("^"),
    REM("%"),
    LSHIFT("<<"),
    PLUSASSIGN("+="),
    MINUSASSIGN("-="),
    STARASSIGN("*="),
    SLASHASSIGN("/="),
    ANDASSIGN("&="),
    ORASSIGN("|="),
    XORASSIGN("^="),
    REMASSIGN("%="),
    LSHIFTASSIGN("<<="),
    RSIGNEDSHIFTASSIGN(">>="),
    RUNSIGNEDSHIFTASSIGN(">>>="),
    ELLIPSIS("..."),
    ARROW("->"),
    DOUBLECOLON("::"),
    RUNSIGNEDSHIFT(">>>"),
    RSIGNEDSHIFT(">>"),
    GT(">"),
    // Keep the last comma
    ;

    public final String image;

    OperatorKind(String image) {
        this.image = image;
    }
}
