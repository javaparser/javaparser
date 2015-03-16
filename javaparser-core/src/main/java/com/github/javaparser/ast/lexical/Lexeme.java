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

import com.github.javaparser.Position;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public abstract class Lexeme {

    private Lexeme previous;
    private Lexeme next;
    private Position begin;
    private Position end;

    public Lexeme() {
    }

    public abstract LexemeKind getLexemeKind();

    public boolean is(LexemeKind first, LexemeKind... rest) {
        return EnumSet.of(first, rest).contains(getLexemeKind());
    }

    public boolean is(CommentKind first, CommentKind... rest) {
        return false;
    }

    public boolean is(KeywordKind first, KeywordKind... rest) {
        return false;
    }

    public boolean is(LiteralKind first, LiteralKind... rest) {
        return false;
    }

    public boolean is(OperatorKind first, OperatorKind... rest) {
        return false;
    }

    public boolean is(SeparatorKind first, SeparatorKind... rest) {
        return false;
    }

    public boolean is(WhitespaceKind first, WhitespaceKind... rest) {
        return false;
    }

    public abstract String image();

    public Position begin() {
        return begin;
    }

    public Position end() {
        return end;
    }

    public Lexeme previous() {
        return (Lexeme) previous;
    }

    public Lexeme next() {
        return (Lexeme) next;
    }

    public void setPrevious(Lexeme previous) {
        this.previous = previous;
    }

    public void setNext(Lexeme next) {
        this.next = next;
    }

    public void setBegin(Position begin) {
        this.begin = begin;
    }

    public void setEnd(Position end) {
        this.end = end;
    }
}
